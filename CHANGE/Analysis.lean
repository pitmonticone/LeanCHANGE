import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Convolution
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Function.Jacobian
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal
noncomputable section

/-
# Example

A sequence `u` of numbers converges to a number `l` if
`∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| < ε`
and a function `f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ ⇒ |f(x) - f(x₀)| < ε`

Fact: if `f` is continuous at `x₀` and `u` converges to `x₀` then
`f ∘ u : n ↦ f(u_n)` converges to `f(x₀)`.
-/

/-- The sequence `u` of real numbers converges to `l`. -/
def SequenceHasLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - l| < ε

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f (x) - f (x₀)| < ε

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (u_lim : SequenceHasLimit u x₀)
    (f_cont : ContinuousAtPoint f x₀) :
    SequenceHasLimit (f ∘ u) (f x₀) := by
  unfold SequenceHasLimit
  -- Let ε > 0 be arbitrary
  intro (ε : ℝ) (hε : ε > 0)
  -- Since `f` is continuous, we can pick a `δ > 0` such that
  -- for all `x`, `|x - x₀| < δ → |f(x) - f(x₀)| < ε`.
  unfold ContinuousAtPoint at f_cont
  obtain ⟨δ, hδ, f_prop⟩ := f_cont ε (by assumption)
  -- Since `u` converges to `x₀`, we can pick a `N` such that
  -- for all `n ≥ N`, `|u_n - x₀| < δ`.
  obtain ⟨N, u_prop⟩ := u_lim δ hδ
  -- We pick this `N` to show that `f ∘ u` has limit `f(x₀)`.
  use N
  -- If `n ≥ N` we have `|u_n - x₀| < δ`,
  intro n hn
  specialize u_prop n hn
  -- hence `|f(u_n) - f(x₀)| < ε`.
  specialize f_prop (u n) u_prop
  -- This finishes the proof.
  assumption


/- # Differential Calculus -/

/- We write `deriv` to compute the derivative of a function.
`simp` can compute the derivatives of standard functions. -/

example (x : ℝ) : deriv Real.sin x = Real.cos x := by simp

example (x : ℂ) : deriv (fun y ↦ Complex.sin (y + 3)) x = Complex.cos (x + 3) := by simp

/- Not every function has a derivative.
As usual, in mathlib we just define the derivative
of a non-differentiable function to be `0`. -/

variable (f : ℝ → ℝ) (x : ℝ) in
#check (deriv_zero_of_not_differentiableAt :
  ¬ DifferentiableAt ℝ f x → deriv f x = 0)

/- So proving that `deriv f x = y` doesn't
necessarily mean that `f` is differentiable.
Often it is nicer to use the predicate `HasDerivAt f y x`,
which states that `f` is differentiable and `f'(x) = y`. -/

example (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x :=
  hasDerivAt_sin x


/- We can also specify that a function has a derivative
without specifying its derivative. -/

example (x : ℝ) : DifferentiableAt ℝ sin x :=
  (hasDerivAt_sin x).differentiableAt


/- Mathlib contains lemmas stating that common operations satisfy
`HasDerivAt` and `DifferentiableAt` and to compute `deriv`. -/

#check HasDerivAt.add
#check deriv_add
#check DifferentiableAt.add


example (x : ℝ) :
    HasDerivAt (fun x ↦ Real.cos x + Real.sin x)
    (Real.cos x - Real.sin x) x := by {
  rw [sub_eq_neg_add]
  apply HasDerivAt.add
  · exact?
  · exact?
  }


/- There are various variations of derivatives/being differentiable -/

/- A function is differentiable everywhere. -/
#check Differentiable

/- A function is differentiable on a subset. -/
#check DifferentiableOn

/- A function is differentiable at a point, considered only within the subset -/
#check DifferentiableWithinAt

/- We can also consider the derivative only within a subset. -/
#check HasDerivWithinAt
#check derivWithin




/-
Lean has the following names for intervals
("c" = closed, "o" = open, "i" = infinity)
Icc a b = [a, b]
Ico a b = [a, b)
Ioc a b = (a, b]
Ioo a b = (a, b)
Ici a   = [a, ∞)
Ioi a   = (a, ∞)
Iic b   = (-∞, b]
Iio b   = (-∞, b)

The intermediate value theorem states that if `f` is continuous and
`f a ≤ y ≤ f b`, then there is an `x ∈ [a, b]` with `f(x) = y`.
-/

example {f : ℝ → ℝ} {a b _y : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b :=
  intermediate_value_Icc hab hf


/-
The mean value theorem states that if `f` is continuus on `[a, b]`
and differentiable on `(a, b)` then there is a `c ∈ (a, b)` where `f'(c)` is the
average slope of `f` on `[a, b]`
-/
example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hf hf'


/- Rolle's theorem is the special case where `f a = f b`.
Why is there no differentiability requirement on `f` here? -/
example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hfc hfI



/- We can more generally talk about the derivative of functions between normed spaces.

A *normed group* is an abelian group with a norm satisfying the following rules.
-/

section NormedGroup

variable {E : Type*} [NormedAddCommGroup E]

#check (fun x ↦ ‖x‖ : E → ℝ)

example (x : E) : 0 ≤ ‖x‖ :=
  norm_nonneg x

example {x : E} : ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

/- This turns `E` into a metric space. -/
example (x y : E) : dist x y = ‖x - y‖ :=
  dist_eq_norm x y

/- A *normed space* is a normed group that is a vector space
satisfying the following condition. -/

variable [NormedSpace ℝ E]

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
  norm_smul a x


/- A complete normed space is known as a *Banach space*.
Every finite-dimensional vector space is complete. -/

example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance

/- In the above examples, we could also replace `ℝ` by `ℂ`
or another *normed field*. -/

end NormedGroup



/- We can also take the derivative of functions that take values in a
normed vector space. -/

example (x : ℝ) : deriv (fun x ↦ ((Real.cos x) ^ 2, (Real.sin x) ^ 2)) x =
    (- 2 * Real.cos x * Real.sin x, 2 * Real.sin x * Real.cos x) := by {
  apply HasDerivAt.deriv
  refine HasDerivAt.prodMk ?h.hf₁ ?h.hf₂
  · convert HasDerivAt.pow _ _ using 1
    rotate_right
    exact hasDerivAt_cos x
    ring
    -- suffices : HasDerivAt (fun x ↦ cos x ^ 2)
    --   (2 * (cos x) ^ 1 * -sin x) x
    -- · simp at this
    --   simp
    --   exact this
    -- apply HasDerivAt.pow
    -- exact hasDerivAt_cos x
  · convert HasDerivAt.pow _ _
    simp
    exact hasDerivAt_sin x
  }

/- If the domain is a normed space we can define the
total derivative, which will be a continuous linear map. -/

/- Morphisms between normed spaces are continuous linear maps `E →L[𝕜] F`. -/
section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]


example : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E

example (f : E →L[𝕜] F) : E → F := f

example (f : E →L[𝕜] F) : Continuous f := f.cont

example (f : E →L[𝕜] F) : E →ₗ[𝕜] F := f

/- Continuous linear maps have an operator norm. -/

example (f : E →L[𝕜] F) (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  f.le_opNorm x

example (f : E →L[𝕜] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  f.opNorm_le_bound hMp hM


/- We define the *Fréchet derivative* of any function between normed spaces. -/

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔
    Tendsto (fun x ↦ ‖f x - f x₀ - f' (x - x₀)‖ / ‖x - x₀‖) (𝓝 x₀) (𝓝 0) := by
  simp_rw [div_eq_inv_mul, hasFDerivAt_iff_tendsto]

#check HasDerivAt
#check HasFDerivAt

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) :
    fderiv 𝕜 f x₀ = f' :=
  hff'.fderiv

/- We can take the directional derivative or partial derivative
by applying the Fréchet derivative to an argument -/
example (x y : ℝ) :
    let f := fun ((x,y) : ℝ × ℝ) ↦ x^2 + x * y
    fderiv ℝ f (x, y) (1, 0) = 2 * x + y := by
  sorry -- exercise


/- We write `ContDiff 𝕜 n f` to say that `f` is `C^n`,
i.e. it is `n`-times continuously differentiable.
Here `n` lives in `ℕ∞`,
which is `ℕ` with an extra top element `⊤` added ("∞").
`fun_prop` can prove that simple functions are
differentiable, C^n, measurable, ...
(though it is not super reliable) -/
variable {f g : E → F} {n : ℕ∞} {r : 𝕜}
example (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun x ↦ (f x, r • f x + g x)) := by
  fun_prop

example : ContDiff 𝕜 0 f ↔ Continuous f := contDiff_zero
#check contDiff_succ_iff_fderiv

-- example {n : ℕ} : ContDiff 𝕜 (n+1) f ↔
--     Differentiable 𝕜 f ∧ ContDiff 𝕜 n (fderiv 𝕜 f) :=
--   contDiff_succ_iff_fderiv

-- example : ContDiff 𝕜 ⊤ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f :=
--   contDiff_top

end NormedSpace





/-! # Integration -/

example (a b : ℝ) : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 := integral_id

example (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦ ∫ t in (0)..x, f t

example (a b : ℝ) : ∫ x in a..b, exp x = exp b - exp a := integral_exp

/- the notation `[[a, b]]` (in namespace `Interval`) means
`uIcc a b`, i.e. the interval from `min a b` to `max a b` -/
example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) :
    ∫ x in a..b, 1 / x = log (b / a) :=
  integral_one_div h

example (a b : ℝ) :
    ∫ x in a..b, exp (x + 3) = exp (b + 3) - exp (a + 3) := by
  simp

/- We have the fundamental theorem of calculus in Lean. -/

/- FTC-1 -/
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

/- FTC-2 -/
example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ}
    (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt h h'

/- We can use this to compute integrals
if we know the antiderivative. -/

example (a b : ℝ) : ∫ x in a..b, exp (x + 3) =
    exp (b + 3) - exp (a + 3) := by {
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
  · intro x hx
    refine HasDerivAt.comp_add_const x 3 ?hderiv.hf
    exact?
  · apply Continuous.intervalIntegrable
    fun_prop
  }




/- The measure of a set lives in the
extended non-negative reals `[0, ∞]`. -/
#check ENNReal
#check ℝ≥0∞
example : ℝ≥0∞ = WithTop {x : ℝ // 0 ≤ x} := rfl
example : (∞ + 5) = ∞ := by simp
example : (∞ * 0) = 0 := by simp


/- More generally, Mathlib develops Lebesgue integration,
which requires measure theory.

The basic notion is that of a "σ-algebra".
A σ-algebra is called `MeasurableSpace` in Lean.
It consists of a collection of sets, called the *measurable* sets.
The empty set is measurable,
and the measurable sets are closed under
complementation and countable unions. -/

variable {X : Type*} [MeasurableSpace X]

example : MeasurableSet (∅ : Set X) :=
  MeasurableSet.empty

example {s : Set X} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

example {f : ℕ → Set X} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h



/-
We now can define measures.

On paper, a measure on a set equipped with a σ-algebra
is a function from the measurable sets to `[0, ∞]`
that is additive on countable disjoint unions.

In Mathlib, we denote `[0, ∞]` by `ENNReal`.
We extend the measure to any set `s`
as the infimum of measures of measurable sets containing `s`.
Of course, many lemmas still require measurability assumptions,
but some can be proven without measurability.
-/

variable {μ : Measure X}

example : μ ∅ = 0 :=
  measure_empty

example {s : ℕ → Set X} (hmeas : ∀ i, MeasurableSet (s i))
    (hdis : Pairwise (Disjoint on s)) :
    μ (⋃ i, s i) = ∑' i, μ (s i) :=
  μ.m_iUnion hmeas hdis

example (s : Set X) : μ s = ⨅ (t ⊇ s) (_h : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ℕ → Set X) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

/- We say that a property `P` holds **almost everywhere**
if the set of elements where it doesn't hold has measure 0. -/
example {P : X → Prop} :
    (∀ᶠ x in ae μ, P x) ↔ μ {x | ¬ P x} = 0 := by
  rfl

/- This also has the specific notation `∀ᵐ (x : X) ∂μ, P x`. -/
variable (P : X → Prop) in
#check ∀ᶠ x in ae μ, P x

/- Various spaces have a canonical measure associated to them,
called `volume`. -/
example : MeasureSpace ℝ := by infer_instance
#check (volume : Measure ℝ)
#check (volume : Measure (Fin 3 → ℝ))

/- The function `ENNReal.toReal` sends `∞` to `0`. -/
example (a b : ℝ) (h : a ≤ b) :
    (volume (Icc a b)).toReal = b - a := by
  simp [h]

/- The collection of measurable sets on `ℝ`
is the smallest σ-algebra containing the open sets.
These are the *Borel-measurable* sets. -/
example : BorelSpace ℝ := by infer_instance


/- The *Lebesgue-measurable* sets are the sets
that are Borel measurable up to a null set. -/
#check NullMeasurableSet
example {s : Set ℝ} (hs : volume s = 0) : NullMeasurableSet s := by
  exact?

/-
Remark: `rw` will not rewrite inside a binder
(like `fun x`, `∃ x`, `∫ x` or `∀ᶠ x`).
Use `simp_rw`, `simp only` or `unfold` instead. -/
example : ∀ᵐ x : ℝ, Irrational x := by {
  simp_rw [Irrational]
  -- unfold Irrational
  refine Countable.ae_notMem ?h volume
  exact countable_range Rat.cast
  }


/- A map is (Borel)-measurable if preimages of measurable sets
under that map are measurable. -/
#print Measurable
#check Continuous.measurable

/- A map `f` into a normed group is integrable when it is measurable and the map
`x ↦ ‖f x‖` has a finite integral. -/
#check Integrable





/- We can take the integrals for functions intro a Banach space.
This version of the integral is called the *Bochner integral*.
The integral is denoted `∫ x, f x ∂μ` -/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {f : X → E}

example {f g : X → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ :=
  integral_add hf hg


/-
* We can write `∫ x in s, f x ∂μ` for the integral restricted to a set.
* In the following example, we compute the integral of a constant map
-/
example {s : Set X} (c : E) :
    ∫ _x in s, c ∂μ = (μ s).toReal • c :=
  setIntegral_const c

/-
* We can abbreviate `∫ x, f x ∂volume` to `∫ x, f x`
* We write `∫ x in a..b, f x ∂μ` for the integral
  on an interval (whose sign is reversed if `b < a`)
-/
example {f : ℝ → E} {a b c : ℝ} : ∫ x in a..b, c • f x = c • ∫ x in a..b, f x :=
  intervalIntegral.integral_smul c f

example {f : ℝ → E} {a b : ℝ} : ∫ x in b..a, f x = - ∫ x in a..b, f x :=
  intervalIntegral.integral_symm a b


/- Here is a version of the dominated convergence theorem. -/
example {F : ℕ → X → E} {f : X → E} (bound : X → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hint : Integrable bound μ) (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim


/- Here is the statement of Fubini's theorem. -/
variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν] in
example (f : X × Y → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf


/- There are various versions of the change of variables theorem. -/
example {s : Set ℝ} {f f' : ℝ → ℝ}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : ℝ → E) : ∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x) :=
  integral_image_eq_integral_abs_deriv_smul hs hf' hf g
