import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix


/--
A `WeightedGraph V W` assigns a weight in `W` to each ordered pair of vertices in `V`.

It is defined as a function `V × V → W`.
The value `0` (when `W` has a `Zero` instance) is interpreted as “no edge”.
-/
structure WeightedGraph (V W : Type) [Zero W] where
  weight : V → V → W

/--
The adjacency matrix of a weighted graph.
-/
@[simp]
def WeightedGraph.adjMatrix {V W : Type} [Zero W] (g : WeightedGraph V W) : Matrix V V W :=
  fun v w => g.weight v w

/--
Adjacency relation induced by a weighted graph.

Two vertices are adjacent iff the corresponding weight is nonzero.
-/
def WeightedGraph.Adj {V W : Type} [Zero W] (g : WeightedGraph V W) (v w : V) : Prop :=
  g.weight v w ≠ 0

/--
A quantum walk graph is defined over a finite vertex set `V` and has complex weights on edges.

The Hermitian condition ensures the adjacency matrix is a valid Hamiltonian
(i.e. corresponds to a self-adjoint operator), which is required for unitary evolution.
-/
structure QWalkGraph (V : Type) [Fintype V] [DecidableEq V] extends g : WeightedGraph V ℂ where
  adjMatrix_hermitian : Matrix.IsHermitian (g.adjMatrix)

def QWalkGraph.of {V : Type} (g : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel g.Adj]
    : QWalkGraph V :=
  { weight := fun v w => if (g.Adj v w) then 1 else 0,
    adjMatrix_hermitian := by
      unfold WeightedGraph.adjMatrix
      simp only [Matrix.IsHermitian, Matrix.conjTranspose, Matrix.transpose]
      funext x y
      simp
      have hxy : g.Adj x y ∨ ¬g.Adj x y := by apply Classical.em
      rcases hxy with (hxy | hxy)
      · simp [hxy]
        exact SimpleGraph.adj_symm g hxy
      · simp [hxy]
        rw [SimpleGraph.adj_comm]
        exact hxy
  }

/--
Uniform mixing at time `t` means that the quantum walk evolution at time `t`
is the completely mixed state (all entries equal).

This is expressed using the matrix exponential of the Hamiltonian `g.adjMatrix`.
-/
def UniformMixingAtTimeT {V : Type} [Fintype V] [DecidableEq V]
    (g : QWalkGraph V) (t : ℝ) : Prop :=
  let U_t := NormedSpace.exp ((Complex.I * t) • g.adjMatrix)
  U_t • U_t.conjTranspose = ((1 : ℂ) / Fintype.card V) • (1 : Matrix V V ℂ)

/--
A quantum walk graph has uniform mixing if there exists
some time `t` at which it has uniform mixing.
-/
def UniformMixing {V : Type} [Fintype V] [DecidableEq V]
    (g : QWalkGraph V) : Prop :=
  ∃ t : ℝ, UniformMixingAtTimeT g t
