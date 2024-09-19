import Optlib.Function.Proximal
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Convex.Extrema

noncomputable section

open Set InnerProductSpace Topology Filter

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} (cf : ConvexOn ℝ univ f)
variable (xm : E)
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

lemma SubderivAt_zero : 0 ∈ SubderivAt f xm ↔ ∀ y, f y ≥ f xm + ⟪0, y - xm⟫:= by rfl

/-
If the objective function f of the unconstrained optimization problem is convex,
then xm is the minimal value of f is equivalent to 0 ∈ ∂f(xm)
-/
theorem first_order_convex_iff_subgradient : IsMinOn f univ xm ↔ 0 ∈ SubderivAt f xm := by
  rw[SubderivAt_zero xm ,isMinOn_iff]
  constructor
  · intro h y
    simp only [inner_zero_left, add_zero, ge_iff_le]
    apply h y
    simp only [mem_univ]
  · intro h x _
    have := h x
    simp only [inner_zero_left, add_zero, ge_iff_le] at this
    exact this
