// The digraph command performs queries over unidled directed graphs
// represented in text form.  It is intended to integrate nicely with
// typical UNIX command pipelines.
//
// Since directed graphs (import graphs, reference graphs, call graphs,
// etc) often arise during software tool development and debugging, this
// command is included in the go.tools repository.
//
// TODO(adonovan):
// - support input files other than stdin
// - suport alternative formats (AT&T GraphViz, CSV, etc),
//   a comment syntax, etc.
// - allow queries to nest, like Blaze query language.
//
package main

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"github.com/owulveryck/toscalib"
	"io"
	"os"
	"sort"
	"strconv"
	"unicode"
	"unicode/utf8"
)

const Usage = `digraph: queries over directed graphs in text form.

Graph format:

  Each line contains zero or more words.  Words are separated by
  unquoted whitespace; words may contain Go-style double-quoted portions,
  allowing spaces and other characters to be expressed.

  Each field declares a node, and if there are more than one,
  an edge from the first to each subsequent one.
  The graph is provided on the standard input.

  For instance, the following (acyclic) graph specifies a partial order
  among the subtasks of getting dressed:

	% cat clothes.txt
	socks shoes
	"boxer shorts" pants
	pants belt shoes
	shirt tie sweater
	sweater jacket
	hat

  The line "shirt tie sweater" indicates the two edges shirt -> tie and
  shirt -> sweater, not shirt -> tie -> sweater.

Supported queries:

  nodes
	the set of all nodes
  degree
	the in-degree and out-degree of each node.
  preds <id> ...
	the set of immediate predecessors of the specified nodes
  succs <id> ...
	the set of immediate successors of the specified nodes
  forward <id> ...
	the set of nodes transitively reachable from the specified nodes
  reverse <id> ...
	the set of nodes that transitively reach the specified nodes
  somepath <id> <id>
	the list of nodes on some arbitrary path from the first node to the second
  allpaths <id> <id>
	the set of nodes on all paths from the first node to the second
  sccs
	all strongly connected components (one per line)
  scc <id>
	the set of nodes nodes strongly connected to the specified one

Example usage:

   Show the transitive closure of imports of the digraph tool itself:
   % go list -f '{{.ImportPath}}{{.Imports}}' ... | tr '[]' '  ' |
         digraph forward golang.org/x/tools/cmd/digraph

   Show which clothes (see above) must be donned before a jacket:
   %  digraph reverse jacket <clothes.txt

`

func main() {
	flag.Parse()

	args := flag.Args()
	if len(args) == 0 {
		fmt.Println(Usage)
		return
	}

	var argsi = []int{}
	for _, i := range args[1:] {
		j, err := strconv.Atoi(i)
		if err != nil {
			panic(err)

		}
		argsi = append(argsi, j)

	}
	if err := digraph(args[0], argsi); err != nil {
		fmt.Fprintf(os.Stderr, "digraph: %s\n", err)
		os.Exit(1)
	}
}

type nodelist []int

func (l nodelist) println(sep string) {
	for i, id := range l {
		if i > 0 {
			fmt.Fprint(stdout, sep)
		}
		fmt.Fprint(stdout, id)
	}
	fmt.Fprintln(stdout)
}

type nodeset map[int]bool

func (s nodeset) sort() nodelist {
	ids := make(nodelist, len(s))
	var i int
	for id := range s {
		ids[i] = id
		i++
	}
	sort.Ints(ids)
	return ids
}

func (s nodeset) addAll(x nodeset) {
	for id := range x {
		s[id] = true
	}
}

// A graph maps nodes to the non-nil set of their immediate successors.
type graph map[int]nodeset

func (g graph) addNode(id int) nodeset {
	edges := g[id]
	if edges == nil {
		edges = make(nodeset)
		g[id] = edges
	}
	return edges
}

func (g graph) addEdges(from int, to ...int) {
	edges := g.addNode(from)
	for _, to := range to {
		g.addNode(to)
		edges[to] = true
	}
}

func (g graph) reachableFrom(roots nodeset) nodeset {
	seen := make(nodeset)
	var visit func(id int)
	visit = func(id int) {
		if !seen[id] {
			seen[id] = true
			for e := range g[id] {
				visit(e)
			}
		}
	}
	for root := range roots {
		visit(root)
	}
	return seen
}

func (g graph) transpose() graph {
	rev := make(graph)
	for id, edges := range g {
		rev.addNode(id)
		for succ := range edges {
			rev.addEdges(succ, id)
		}
	}
	return rev
}

func (g graph) sccs() []nodeset {
	// Kosaraju's algorithm---Tarjan is overkill here.

	// Forward pass.
	S := make(nodelist, 0, len(g)) // postorder stack
	seen := make(nodeset)
	var visit func(id int)
	visit = func(id int) {
		if !seen[id] {
			seen[id] = true
			for e := range g[id] {
				visit(e)
			}
			S = append(S, id)
		}
	}
	for id := range g {
		visit(id)
	}

	// Reverse pass.
	rev := g.transpose()
	var scc nodeset
	seen = make(nodeset)
	var rvisit func(id int)
	rvisit = func(id int) {
		if !seen[id] {
			seen[id] = true
			scc[id] = true
			for e := range rev[id] {
				rvisit(e)
			}
		}
	}
	var sccs []nodeset
	for len(S) > 0 {
		top := S[len(S)-1]
		S = S[:len(S)-1] // pop
		if !seen[top] {
			scc = make(nodeset)
			rvisit(top)
			sccs = append(sccs, scc)
		}
	}
	return sccs
}

func parse(rd io.Reader) (graph, toscalib.ToscaDefinition, error) {
	g := make(graph)
	// Parse the input graph.
	var t toscalib.ToscaDefinition
	err := t.Parse(rd)
	if err != nil {
		return nil, t, err
	}
	adjacencyMatrix := t.AdjacencyMatrix
	//g.addEdges(node)
	row, col := adjacencyMatrix.Dims()
	for r := 1; r < row; r++ {
		for c := 1; c < col; c++ {
			if adjacencyMatrix.At(r, c) == 1 {
				g.addEdges(r, c)
			}
		}
	}
	return g, t, nil
}

var stdin io.Reader = os.Stdin
var stdout io.Writer = os.Stdout

func digraph(cmd string, args []int) error {
	// Parse the input graph.
	g, _, err := parse(stdin)
	if err != nil {
		return err
	}

	// Parse the command line.
	switch cmd {
	case "nodes":
		if len(args) != 0 {
			return fmt.Errorf("usage: digraph nodes")
		}
		nodes := make(nodeset)
		for id := range g {
			nodes[id] = true
		}
		nodes.sort().println("\n")

	case "degree":
		if len(args) != 0 {
			return fmt.Errorf("usage: digraph degree")
		}
		nodes := make(nodeset)
		for id := range g {
			nodes[id] = true
		}
		rev := g.transpose()
		for _, id := range nodes.sort() {
			fmt.Fprintf(stdout, "%d\t%d\t%s\n", len(rev[id]), len(g[id]), id)
		}

	case "succs", "preds":
		if len(args) == 0 {
			return fmt.Errorf("usage: digraph %s <id> ...", cmd)
		}
		g := g
		if cmd == "preds" {
			g = g.transpose()
		}
		result := make(nodeset)
		for _, root := range args {
			edges := g[root]
			if edges == nil {
				return fmt.Errorf("no such node %q", root)
			}
			result.addAll(edges)
		}
		result.sort().println("\n")

	case "forward", "reverse":
		if len(args) == 0 {
			return fmt.Errorf("usage: digraph %s <id> ...", cmd)
		}
		roots := make(nodeset)
		for _, root := range args {
			if g[root] == nil {
				return fmt.Errorf("no such node %q", root)
			}
			roots[root] = true
		}
		g := g
		if cmd == "reverse" {
			g = g.transpose()
		}
		g.reachableFrom(roots).sort().println("\n")

	case "somepath":
		if len(args) != 2 {
			return fmt.Errorf("usage: digraph somepath <from> <to>")
		}
		from, to := args[0], args[1]
		if g[from] == nil {
			return fmt.Errorf("no such 'from' node %q", from)
		}
		if g[to] == nil {
			return fmt.Errorf("no such 'to' node %q", to)
		}

		seen := make(nodeset)
		var visit func(path nodelist, id int) bool
		visit = func(path nodelist, id int) bool {
			if !seen[id] {
				seen[id] = true
				if id == to {
					append(path, id).println("\n")
					return true // unwind
				}
				for e := range g[id] {
					if visit(append(path, id), e) {
						return true
					}
				}
			}
			return false
		}
		if !visit(make(nodelist, 0, 100), from) {
			return fmt.Errorf("no path from %q to %q", args[0], args[1])
		}

	case "allpaths":
		if len(args) != 2 {
			return fmt.Errorf("usage: digraph allpaths <from> <to>")
		}
		from, to := args[0], args[1]
		if g[from] == nil {
			return fmt.Errorf("no such 'from' node %q", from)
		}
		if g[to] == nil {
			return fmt.Errorf("no such 'to' node %q", to)
		}

		seen := make(nodeset) // value of seen[x] indicates whether x is on some path to 'to'
		var visit func(id int) bool
		visit = func(id int) bool {
			reachesTo, ok := seen[id]
			if !ok {
				reachesTo = id == to

				seen[id] = reachesTo
				for e := range g[id] {
					if visit(e) {
						reachesTo = true
					}
				}
				seen[id] = reachesTo
			}
			return reachesTo
		}
		if !visit(from) {
			return fmt.Errorf("no path from %q to %q", from, to)
		}
		for id, reachesTo := range seen {
			if !reachesTo {
				delete(seen, id)
			}
		}
		seen.sort().println("\n")

	case "sccs":
		if len(args) != 0 {
			return fmt.Errorf("usage: digraph sccs")
		}
		for _, scc := range g.sccs() {
			scc.sort().println(" ")
		}

	case "scc":
		if len(args) != 1 {
			return fmt.Errorf("usage: digraph scc <id>")
		}
		id := args[0]
		if g[id] == nil {
			return fmt.Errorf("no such node %q", id)
		}
		for _, scc := range g.sccs() {
			if scc[id] {
				scc.sort().println("\n")
				break
			}
		}

	default:
		return fmt.Errorf("no such command %q", cmd)
	}

	return nil
}

// -- Utilities --------------------------------------------------------

// split splits a line into words, which are generally separated by
// spaces, but Go-style double-quoted string literals are also supported.
// (This approximates the behaviour of the Bourne shell.)
//
//   `one "two three"` -> ["one" "two three"]
//   `a"\n"b` -> ["a\nb"]
//
func split(line string) ([]string, error) {
	var (
		words   []string
		inWord  bool
		current bytes.Buffer
	)

	for len(line) > 0 {
		r, size := utf8.DecodeRuneInString(line)
		if unicode.IsSpace(r) {
			if inWord {
				words = append(words, current.String())
				current.Reset()
				inWord = false
			}
		} else if r == '"' {
			var ok bool
			size, ok = quotedLength(line)
			if !ok {
				return nil, errors.New("invalid quotation")
			}
			s, err := strconv.Unquote(line[:size])
			if err != nil {
				return nil, err
			}
			current.WriteString(s)
			inWord = true
		} else {
			current.WriteRune(r)
			inWord = true
		}
		line = line[size:]
	}
	if inWord {
		words = append(words, current.String())
	}
	return words, nil
}

// quotedLength returns the length in bytes of the prefix of input that
// contain a possibly-valid double-quoted Go string literal.
//
// On success, n is at least two (""); input[:n] may be passed to
// strconv.Unquote to interpret its value, and input[n:] contains the
// rest of the input.
//
// On failure, quotedLength returns false, and the entire input can be
// passed to strconv.Unquote if an informative error message is desired.
//
// quotedLength does not and need not detect all errors, such as
// invalid hex or octal escape sequences, since it assumes
// strconv.Unquote will be applied to the prefix.  It guarantees only
// that if there is a prefix of input containing a valid string literal,
// its length is returned.
//
// TODO(adonovan): move this into a strconv-like utility package.
//
func quotedLength(input string) (n int, ok bool) {
	var offset int

	// next returns the rune at offset, or -1 on EOF.
	// offset advances to just after that rune.
	next := func() rune {
		if offset < len(input) {
			r, size := utf8.DecodeRuneInString(input[offset:])
			offset += size
			return r
		}
		return -1
	}

	if next() != '"' {
		return // error: not a quotation
	}

	for {
		r := next()
		if r == '\n' || r < 0 {
			return // error: string literal not terminated
		}
		if r == '"' {
			return offset, true // success
		}
		if r == '\\' {
			var skip int
			switch next() {
			case 'a', 'b', 'f', 'n', 'r', 't', 'v', '\\', '"':
				skip = 0
			case '0', '1', '2', '3', '4', '5', '6', '7':
				skip = 2
			case 'x':
				skip = 2
			case 'u':
				skip = 4
			case 'U':
				skip = 8
			default:
				return // error: invalid escape
			}

			for i := 0; i < skip; i++ {
				next()
			}
		}
	}
}
