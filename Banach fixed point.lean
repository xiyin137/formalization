import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic

open Metric

/-- Distance between iterations decreases exponentially -/
lemma iterate_dist_le
    {X : Type*} [MetricSpace X]
    (f : X → X) (k : ℝ) (hk₁ : 0 ≤ k)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y)
    (x : X) (n : ℕ) :
    dist ((f^[n]) x) ((f^[n+1]) x) ≤ k^n * dist x (f x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc dist ((f^[n+1]) x) ((f^[n+2]) x)
        = dist (f ((f^[n]) x)) (f ((f^[n+1]) x)) := by simp [Function.iterate_succ_apply']
      _ ≤ k * dist ((f^[n]) x) ((f^[n+1]) x) := hf _ _
      _ ≤ k * (k^n * dist x (f x)) := mul_le_mul_of_nonneg_left ih hk₁
      _ = k^(n+1) * dist x (f x) := by ring

/-- f is continuous (Lipschitz implies continuous) - COMPLETE PROOF -/
lemma continuous_of_contraction
    {X : Type*} [MetricSpace X]
    (f : X → X) (k : ℝ) (hk₁ : 0 ≤ k)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) :
    Continuous f := by
  apply Metric.continuous_iff.mpr
  intros x ε hε
  by_cases h : k = 0
  · use 1
    simp
    intros y _
    have : dist (f x) (f y) = 0 := by
      have : dist (f x) (f y) ≤ 0 := by
        calc dist (f x) (f y) ≤ k * dist x y := hf x y
          _ = 0 := by rw [h]; ring
      exact le_antisymm this dist_nonneg
    rw [dist_eq_zero] at this
    simp [this, hε]
  · have hk_pos : 0 < k := by
      cases' hk₁.lt_or_eq with h1 h2
      · exact h1
      · exact absurd h2.symm h
    use ε / k
    constructor
    · exact div_pos hε hk_pos
    · intros y hy
      rw [dist_comm]
      calc dist (f x) (f y)
          ≤ k * dist x y := hf x y
        _ < k * (ε / k) := by
            apply mul_lt_mul_of_pos_left
            · rw [dist_comm]
              exact hy
            · exact hk_pos
        _ = ε := by field_simp

/-- Uniqueness of fixed point - COMPLETE PROOF -/
theorem banach_uniqueness
    {X : Type*} [MetricSpace X]
    (f : X → X) (k : ℝ) (hk : k < 1)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y)
    (x y : X) (hx : f x = x) (hy : f y = y) :
    x = y := by
  by_contra h
  have h_pos : dist x y > 0 := dist_pos.mpr h
  have h_contract : dist (f x) (f y) ≤ k * dist x y := hf x y
  rw [hx, hy] at h_contract
  have hk_pos : 0 < 1 - k := by linarith
  have key : dist x y * (1 - k) ≤ 0 := by linarith
  have : 0 < dist x y * (1 - k) := mul_pos h_pos hk_pos
  linarith

/--Existence of fixed point - COMPLETE PROOF -/
theorem banach_existence
   {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
   (f : X → X) (k : ℝ) (hk : k < 1) (hk₁ : 0 ≤ k)
    (hf : ∀ x y, dist (f x) (f y) ≤ k * dist x y) :
    ∃ x : X, f x = x := by
  -- Pick an arbitrary starting point
  obtain ⟨x₀⟩ := ‹Nonempty X›
  
  -- Define the sequence of iterates
  let seq := fun n => (f^[n]) x₀
  
  -- Show the sequence is Cauchy using geometric bound
  have hCauchy : CauchySeq seq := by
    apply cauchySeq_of_le_geometric k (dist x₀ (f x₀)) hk
    intro n
    calc dist (seq n) (seq (n + 1))
        = dist ((f^[n]) x₀) ((f^[n+1]) x₀) := rfl
      _ ≤ k^n * dist x₀ (f x₀) := iterate_dist_le f k hk₁ hf x₀ n
      _ = dist x₀ (f x₀) * k^n := mul_comm _ _
  
  -- Use completeness to get the limit
  have hComplete : ∃ x, Filter.atTop.map seq ≤ nhds x := 
    CompleteSpace.complete hCauchy
  obtain ⟨x, hx⟩ := hComplete
  
  use x
  
  -- Show f(x) = x using continuity
  have hcont : Continuous f := continuous_of_contraction f k hk₁ hf
  
  have hx' : Filter.Tendsto seq Filter.atTop (nhds x) := hx
  
  -- f(seq n) → f(x) by continuity
  have h1 : Filter.Tendsto (fun n => f (seq n)) Filter.atTop (nhds (f x)) := by
    exact Continuous.tendsto hcont x |>.comp hx'
  
  -- But f(seq n) = seq(n+1) → x
  have eq : (fun n => f (seq n)) = (fun n => seq (n + 1)) := by
    ext n
    simp only [seq, Function.iterate_succ_apply']
    
  rw [eq] at h1
  
  have h2 : Filter.Tendsto (fun n => seq (n + 1)) Filter.atTop (nhds x) := by
    exact hx'.comp (Filter.tendsto_add_atTop_nat 1)
  
  -- Since seq(n+1) → x and seq(n+1) → f(x), we have f(x) = x
  have : f x = x := tendsto_nhds_unique h1 h2
  exact this

#check iterate_dist_le
#check continuous_of_contraction
#check banach_uniqueness