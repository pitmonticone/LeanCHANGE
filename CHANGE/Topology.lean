import Mathlib.Tactic
open BigOperators Function Set Filter Topology TopologicalSpace MeasureTheory

/- # Limits -/


/-
In topology, one of basic concepts is that of a limit.
Say `f : ℝ → ℝ`. There are many variants of limits.
* the limit of `f(x)` as `x` tends to `x₀`
* the limit of `f(x)` as `x` tends to `∞` or `-∞`
* the limit of `f(x)` as `x` tends to `x₀⁻` or `x₀⁺`
* variations of the above with the additional assumption that `x ≠ x₀`.

This gives 8 different notions of behavior of `x`.
Similarly, the value `f(x)` can have the same behavior:
`f(x)` tends to `∞`, `-∞`, `x₀`, `x₀⁺`, ...

This gives `64` notions of limits.

When we prove that two limits compose: if
`f x` tends to `y₀` when `x` tends to `x₀` and
`g y` tends to `z₀` when `y` tends to `y₀` then
`(g ∘ f) x` tends to `z₀` when `x` tends to `x₀`.
This lemma has 512 variants.

Obviously we don't want to prove this 512 times.
Solution: use filters.

If `X` is a type, a filter `F : Filter X` is a
collection of sets `F.sets : Set (Set X)` satisfying the following:
-/
section Filter

variable {X Y : Type*} (F : Filter X)

#check (F.sets : Set (Set X))
#check (F.univ_sets : univ ∈ F.sets)
#check (F.sets_of_superset : ∀ {U V},
  U ∈ F.sets → U ⊆ V → V ∈ F.sets)
#check (F.inter_sets : ∀ {U V},
  U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets)

end Filter


/- Operations on filters -/

/- the *pushforward* of filters generalizes images of sets. -/
example {X Y : Type*} (f : X → Y) : Filter X → Filter Y :=
  Filter.map f

example {X Y : Type*} (f : X → Y) (F : Filter X) (V : Set Y) :
    V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F := by
  rfl

/- the *pullback* of filters generalizes preimages -/
example {X Y : Type*} (f : X → Y) : Filter Y → Filter X :=
  Filter.comap f


/- Using these operations, we can define the limit. -/
def MyTendsto {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

def Tendsto_iff {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ ∀ S : Set Y, S ∈ G → f ⁻¹' S ∈ F := by
  rfl

/- A sequence `u` converges to `x` -/
example (u : ℕ → ℝ) (x : ℝ) : Prop :=
  Tendsto u atTop (𝓝 x)

/- `\lim_{x → x₀} f(x) = y₀` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝 x₀) (𝓝 y₀)

/- `\lim_{x → x₀⁻, x ≠ x₀} f(x) = y₀⁺` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝[<] x₀) (𝓝[≥] y₀)

/- Now the following states all possible composition lemmas all at
once! -/
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z}
    {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H := by {
  rw [Tendsto] at *
  calc
    map (g ∘ f) F = map g (map f F) := rfl
    _ ≤ map g G := by
      --apply map_mono hf
      gcongr
    _ ≤ H := hg

  }

/-
Filters also allow us to reason about things that are
"eventually true". If `F : Filter X` and `P : X → Prop` then
`∀ᶠ n in F, P n` means that `P n` is eventually true for `n` in `F`.
It is defined to be `{ x | P x } ∈ F`.

The following example shows that if `P n` and `Q n` hold for
sufficiently large `n`, then so does `P n ∧ Q n`.
-/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ





section Topology

/- Let's look at the definition of topological space. -/

universe u v
variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]


example {ι : Type*} (s : ι → Set X) :
    interior (⋂ i, s i) ⊆ ⋂ i, interior (s i) := by {
  simp only [subset_iInter_iff]
  intro i x hx
  --rw [mem_interior] at hx ⊢
  apply interior_mono _ hx
  exact iInter_subset_of_subset i fun ⦃a⦄ a ↦ a
  }









/- A map between topological spaces is continuous if the
preimages of open sets are open. -/
example {f : X → Y} :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

/- It is equivalent to saying that for any `x₀` the function
value `f x` tends to `f x₀` whenever `x` tends to `x₀`. -/
example {f : X → Y} :
    Continuous f ↔ ∀ x₀, Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  exact continuous_iff_continuousAt

/- By definition, the right-hand side states that `f` is
continuous at `x₀`. -/
example {f : X → Y} {x₀ : X} :
    ContinuousAt f x₀ ↔ Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  rfl







/- Neighborhoods are characterized by the following lemma. -/
example {x : X} {s : Set X} :
    s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff

example {x : X} {s : Set X} (h : s ∈ 𝓝 x) : x ∈ s := by
  rw [mem_nhds_iff] at h
  obtain ⟨U, hUs, hUopen, hUx⟩ := h
  exact hUs hUx








/- We can state that a topological space satisfies
separatedness axioms. -/

example : T0Space X ↔ Injective (𝓝 : X → Filter X) := by
  exact t0Space_iff_nhds_injective X

example : T1Space X ↔ ∀ x, IsClosed ({ x } : Set X) :=
  ⟨by exact fun a x ↦ isClosed_singleton, by exact fun a ↦ { t1 := a }⟩

example : T2Space X ↔
    ∀ x y : X, x ≠ y → Disjoint (𝓝 x) (𝓝 y) :=
  t2Space_iff_disjoint_nhds

example : RegularSpace X ↔ ∀ {s : Set X} {a},
    IsClosed s → a ∉ s → Disjoint (𝓝ˢ s) (𝓝 a) := by
  exact regularSpace_iff X










/- A set is compact if every open cover has a finite subcover. -/

example {K : Set X} : IsCompact K ↔ ∀ {ι : Type u}
    (U : ι → Set X), (∀ i, IsOpen (U i)) → (K ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i := by
  exact isCompact_iff_finite_subcover

#check CompactSpace

/-
This can also be reformulated using filters.
* `NeBot F` iff `F ≠ ⊥` iff `∅ ∉ F`
* `ClusterPt x F` means that `F` has nontrivial intersection
  with `𝓝 x` (viewed as a generalized sets).
* `K` is compact iff every nontrivial filter that contains `K`
  has a cluster point in `K`.
-/

example (F : Filter X) : NeBot F ↔ F ≠ ⊥ := by
  exact?

example {x : X} (F : Filter X) :
    ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) := by
  rfl

example {K : Set X} : IsCompact K ↔
    ∀ {F} [NeBot F], F ≤ 𝓟 K → ∃ x ∈ K, ClusterPt x F := by
  rfl

end Topology



section Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/- A metric space is a type `X` equipped with a distance function
`dist : X → X → ℝ` with the following properties. -/

#check (dist : X → X → ℝ)
#check (dist_nonneg : ∀ {a b : X}, 0 ≤ dist a b)
#check (dist_eq_zero : ∀ {a b : X}, dist a b = 0 ↔ a = b)
#check (dist_comm : ∀ (a b : X), dist a b = dist b a)
#check (dist_triangle : ∀ (a b c : X), dist a c ≤ dist a b + dist b c)

/- In metric spaces, all topological notions are also
characterized by the distance function. -/

example (f : X → Y) (x₀ : X) : ContinuousAt f x₀ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ {x},
    dist x x₀ < δ → dist (f x) (f x₀) < ε :=
  Metric.continuousAt_iff

example (x : X) (ε : ℝ) :
    Metric.ball x ε = { y | dist y x < ε } := by
  rfl

example (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

end Metric
