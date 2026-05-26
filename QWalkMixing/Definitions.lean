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
  g.weight

/--
Adjacency relation induced by a weighted graph.

Two vertices are adjacent iff the corresponding weight is nonzero.
-/
@[simp]
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
      funext x y
      by_cases hxy : g.Adj x y
      · simp [hxy, SimpleGraph.adj_comm]
      · simp [hxy, SimpleGraph.adj_comm]
  }

/--
Unitary evolution of the quantum walk at time t is given
by the matrix exponential of the Hamiltonian (adjacency matrix)
-/
noncomputable def QWalkGraph.U {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    : ℝ → Matrix V V ℂ :=
  fun (t : ℝ) => NormedSpace.exp ((Complex.I * t) • g.adjMatrix)

/--
Mixing matrix at time t

Define the mixing matrix M t as the entrywise norm squared of the unitary evolution U at t.
-/
noncomputable def QWalkGraph.M {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V)
    : ℝ → Matrix V V ℝ :=
  fun (t : ℝ) => Matrix.of (g.U t).map Complex.normSq

/--
The Hadamard product of two matrices A and B is the entrywise product.
-/
@[simp]
def HadamardProduct {V W : Type} [Mul W] (A B : Matrix V V W) : Matrix V V W :=
  fun i j => A i j * B i j
/--
The mixing matrix definition is equivalent to the definition of
`M` as the Hadamard product of `U` and `U`'s conjugate
However, this definition would force our matrix to be complex-valued or require
some extra work to show that the result is real-valued, so we stick with the original definition.
-/
lemma M_alternative_def_eq {V : Type} [Fintype V] [DecidableEq V] (g : QWalkGraph V) :
    ∀ (t : ℝ), (g.M t).map Complex.ofReal = HadamardProduct (g.U t) ((g.U t).map star) := by
  intro t
  unfold QWalkGraph.M
  simp only [RCLike.star_def]
  funext i j
  simp only [Matrix.map_apply, Matrix.of_apply, HadamardProduct]
  rw [Complex.normSq_eq_conj_mul_self, mul_comm]

/--
Perfect state transfer at time `t` from vertex `a` to vertex `b` means that
the mixing matrix entry `M t b a` is 1.
-/
def PSTAtTimeT {V : Type} [Fintype V] [DecidableEq V]
    (g : QWalkGraph V) (a b : V) (t : ℝ) : Prop :=
   g.M t b a = 1

/--
Perfect state transfer from vertex `a` to vertex `b` means that there exists some time `t`
at which perfect state transfer occurs.
-/
def PST {V : Type} [Fintype V] [DecidableEq V]
    (g : QWalkGraph V) (a b : V) : Prop :=
  ∃ t : ℝ, PSTAtTimeT g a b t

/--
Uniform mixing at time `t` means that the quantum walk at time `t`
is the completely mixed state (all entries equal).

This is expressed using the mixing matrix `M t`,
which is the Hadamard product of `U t` and its conjugate transpose.
-/
def UniformMixingAtTimeT {V : Type} [Fintype V] [DecidableEq V]
    (g : QWalkGraph V) (t : ℝ) : Prop :=
  g.M t = fun _ _ => (1 : ℝ) / Fintype.card V

/--
A quantum walk graph has uniform mixing if there exists
some time `t` at which it has uniform mixing.
-/
def UniformMixing {V : Type} [Fintype V] [DecidableEq V]
    (g : QWalkGraph V) : Prop :=
  ∃ t : ℝ, UniformMixingAtTimeT g t

def QWalkGraph.switchingEquivalent {V : Type} [Fintype V] [DecidableEq V]
    (g h : QWalkGraph V) : Prop :=
    ∃ (x : V → ℂ),
    (Matrix.diagonal x).conjTranspose * g.adjMatrix * (Matrix.diagonal x) = h.adjMatrix
