import Mathlib.LinearAlgebra.LinearIndependent

/-
# Informal statement

Let `K` be a field and `V` be a vector space over `K`.
Let `f` be a linear map from a vector space `V` to itself.
Let `μ` and `ν` be two scalars such that `μ ≠ ν`.
Let `x` and `y` be two vectors in `V` such that `x ≠ 0` and `y ≠ 0`.
If `f x = μ • x` and `f y = ν • y`, then `x` and `y` are linearly independent.

# Informal proof

Assume that `a` and `b` are two scalars such that `a • x + b • y = 0`.
Then we have `(μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) = 0`.
-/

-- Let `K` be a field and `V` be a vector space over `K`.
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
-- Let `f` be a linear map from a vector space `V` to itself.
variable (f : V →ₗ[K] V)
-- Let `μ` and `ν` be two scalars such that `μ ≠ ν`.
variable (μ ν : K) (hμν : μ ≠ ν)
-- Let `x` and `y` be two vectors in `V` such that `x ≠ 0` and `y ≠ 0`.
variable (x y : V) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0)
-- Let `a` and `b` be two scalars.
variable (a b : K)

example (hx : f x = μ • x) (hy : f y = ν • y) :
    a • x + b • y = 0 → a = 0 ∧ b = 0 := by
  -- Assume `a • x + b • y = 0`.
  intro hab
  --Then we have `(μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) = 0`.
  have :=
    calc
      (μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) := by module
      _ = f (a • x + b • y) - ν • (a • x + b • y) := by simp [hx, hy]
      _ = 0 := by simp [hab]
  simp_all [sub_eq_zero]

/- # Automation

Zoom in a single step of the calculation in teh above proof, with the direction of
the equality reversed.
-/

example (hx : f x = μ • x) (hy : f y = ν • y) :
    f (a • x + b • y) = (a • μ • x + b • ν • y) := by
    calc
      f (a • x + b • y) = f (a • x) + f (b • y) := by rw [map_add] -- @[simp]
      _ = a • f x + b • f y := by rw [map_smul, map_smul]
      _ = (a • μ • x + b • ν • y) := by rw [hx, hy]

/- # Generalisation
The proof never mentions inverses of scalars, so it should work for a larger class of rings.

Try to replace the vector space `V` by an arbitrary module `M`.
-/

-- Let `R` be a ring and `M` be a module over `R`.
variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
-- Let `f` be a linear map from a module `M` to itself.
variable (f : M →ₗ[R] M)
-- Let `μ` and `ν` be two scalars such that `μ ≠ ν`.
variable (μ ν : R) (hμν : μ ≠ ν)
-- Let `x` and `y` be two vectors in `M` such that `x ≠ 0` and `y ≠ 0`.
variable (x y : M) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0)
-- Let `a` and `b` be two scalars.
variable (a b : R)

-- `UNCOMMENT THIS BLOCK`
-- example (hx : f x = μ • x) (hy : f y = ν • y) :
--     a • x + b • y = 0 → a = 0 ∧ b = 0 := by
--   -- Assume `a • x + b • y = 0`.
--   intro hab
--   --Then we have `(μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) = 0`.
--   have :=
--     calc
--       (μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) := by module
--       _ = f (a • x + b • y) - ν • (a • x + b • y) := by simp [hx, hy]
--       _ = 0 := by simp [hab]
--   -- This step uses the result of the calculation steps together with the
--   -- assumptions `hμν : μ ≠ ν` and `hx0 : x ≠ 0` to prove that `a = 0`.
--   simp_all [sub_eq_zero]

/- Lean complains at the first step which requires `b • ν • y = ν • b • y`. We can address this
by assuming that the ring of scalars is commutative.

We need the additional property that `r • m = 0` implies that `r = 0` or `m = 0`
for every `r` in `R` and `m` in `M`.
-/

-- Let `R` be a ring and `M` be a module over `R`.
variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
-- Let `f` be a linear map from a module `M` to itself.
variable (f : M →ₗ[R] M)
-- Let `μ` and `ν` be two scalars such that `μ ≠ ν`.
variable (μ ν : R) (hμν : μ ≠ ν)
-- Let `x` and `y` be two vectors in `M` such that `x ≠ 0` and `y ≠ 0`.
variable (x y : M) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0)
-- Let `a` and `b` be two scalars.
variable (a b : R)

example (hx : f x = μ • x) (hy : f y = ν • y) :
    a • x + b • y = 0 → a = 0 ∧ b = 0 := by
  -- Assume `a • x + b • y = 0`.
  intro hab
  --Then we have `(μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) = 0`.
  have :=
    calc
      (μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) := by module
      _ = f (a • x + b • y) - ν • (a • x + b • y) := by simp [hx, hy]
      _ = 0 := by simp [hab]
  simp_all [sub_eq_zero]
