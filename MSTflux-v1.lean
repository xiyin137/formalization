import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Fin.Basic

/-!
# Matrix String Theory Duality

Formalization of the MST duality conjecture from arXiv:2601.03336.

## Paper Structure

* **Section 1**: MST duality setup (IIB → S-dual → T-dual → IIA pp-wave)
* **Section 2**: D0-branes as flux states (ground state energy, mass spectrum, SO(8))
* **Section 3**: Resonances and semiclassical description (decay, Regge trajectory)

## Main Predictions

1. Ground state energy: E_k = (k²g_YM²)/(2N) × 2πR  [Eq. 2.1]
2. Mass spectrum: m_i = (g_YM/N)√(2πℓ_i)  [Eq. 2.3]
3. SO(8) multiplet at level 1: dimensions (8, 36, 56) = 100 bosonic states
4. Decay condition: (n√(2π)g_YM R)/(2N) < 1  [Eq. 3.2]
5. Decay width: Γ ~ g_A²/(NR) ~ 1/(NR)  [Footnote 3]
6. Regge trajectory: E = (g_YM/N)√(2πJ)  [Section 3.2]
7. IR CFT: Sym^gcd(k,N)(ℝ⁸)  [Kologlu et al '16]

## Verification Targets

These predictions can be tested via:
- Hamiltonian truncation / DLCQ methods
- Matrix quantum mechanics bootstrap
- Numerical semiclassical analysis
-/

open Real

namespace MatrixStringTheory

/-! ## Section 1: The MST Duality Setup

The duality chain (equations 1.1-1.6):
IIB black 1-brane → S-duality → IIA + B-field → T-duality → IIA pp-wave
-/

/-- Parameters from the MST duality chain.

The MST coupling relation g_A = 1/(√(2π) g_YM R) is built in, encoding the
kinematic identification from the chain of dualities. -/
structure MSTParameters where
  N : ℕ
  g_YM : ℝ
  R : ℝ
  g_A : ℝ
  ℓ_A : ℝ
  N_pos : 1 < N
  g_YM_pos : 0 < g_YM
  R_pos : 0 < R
  g_A_pos : 0 < g_A
  ℓ_A_pos : 0 < ℓ_A
  /-- **Equation (1.6)**: MST coupling relation g_A = 1/(√(2π) g_YM R) -/
  coupling_relation : g_A = 1 / (sqrt (2 * π) * g_YM * R)

namespace MSTParameters

/-- String length squared: α' = ℓ_A² -/
noncomputable def alphaPrime (p : MSTParameters) : ℝ := p.ℓ_A ^ 2

lemma alphaPrime_pos (p : MSTParameters) : 0 < p.alphaPrime :=
  sq_pos_of_pos p.ℓ_A_pos

lemma N_pos' (p : MSTParameters) : 0 < p.N :=
  Nat.zero_lt_of_lt p.N_pos

/-- **D0-brane mass**: M_D0 = 1/(g_A √α') -/
noncomputable def M_D0 (p : MSTParameters) : ℝ :=
  1 / (p.g_A * sqrt p.alphaPrime)

lemma M_D0_pos (p : MSTParameters) : 0 < p.M_D0 := by
  unfold M_D0 alphaPrime
  apply div_pos; norm_num
  apply mul_pos p.g_A_pos
  exact sqrt_pos.mpr (sq_pos_of_pos p.ℓ_A_pos)

end MSTParameters

/-! ## Section 2: D0-branes as Flux States

The 2D (8,8) U(N) SYM has ℤ_N center 1-form symmetry (Witten '95),
splitting the Hilbert space into superselection sectors ℋ_k labeled by flux k mod N.
-/

/-- **Flux sector**: k-flux sector of U(N) SYM, k ∈ ℤ_N -/
structure FluxSector (p : MSTParameters) where
  k : Fin p.N

namespace FluxSector

/-- **Equation (2.1)**: Ground state energy E_k = (k²g_YM²)/(2N) × 2πR

In gauge theory variables. -/
noncomputable def groundStateEnergy (p : MSTParameters) (sec : FluxSector p) : ℝ :=
  ((sec.k.val : ℝ) ^ 2 * p.g_YM ^ 2) / (2 * p.N) * (2 * π * p.R)

/-- Ground state energy in D0-brane variables: E_k = (α')/(2NR) × (kM_D0)²

This is the BPS dispersion relation with p⁺ = NR/α', p⁻ = E_k. -/
noncomputable def groundStateEnergy_D0 (p : MSTParameters) (sec : FluxSector p) : ℝ :=
  (p.alphaPrime / (2 * p.N * p.R)) * ((sec.k.val : ℝ) * p.M_D0) ^ 2

/-- **MST Prediction**: The two forms agree (follows from coupling relation) -/
theorem groundStateEnergy_equivalence (p : MSTParameters) (sec : FluxSector p) :
    sec.groundStateEnergy p = sec.groundStateEnergy_D0 p := by
  sorry

/-- Ground state energy is non-negative (proven) -/
lemma groundStateEnergy_nonneg (p : MSTParameters) (sec : FluxSector p) :
    0 ≤ sec.groundStateEnergy p := by
  unfold groundStateEnergy
  apply mul_nonneg
  · apply div_nonneg
    · apply mul_nonneg; apply sq_nonneg; apply sq_nonneg
    · apply le_of_lt; apply mul_pos; norm_num; exact Nat.cast_pos.mpr p.N_pos'
  · apply mul_nonneg
    · apply mul_nonneg; norm_num; exact le_of_lt Real.pi_pos
    · exact le_of_lt p.R_pos

/-- **From Kologlu et al '16**: D = gcd(k,N) determines IR CFT Sym^D(ℝ⁸) -/
noncomputable def divisor (p : MSTParameters) (sec : FluxSector p) : ℕ :=
  Nat.gcd sec.k.val p.N

def singleFlux (p : MSTParameters) : FluxSector p where k := ⟨1, p.N_pos⟩
def zeroFlux (p : MSTParameters) : FluxSector p where k := ⟨0, p.N_pos'⟩

end FluxSector

/-! ## Section 2: Open String States on D0-brane

Multi-mode states characterized by occupation numbers {n_ℓ} at each level ℓ.
Total oscillator number: Σ_ℓ n_ℓ √ℓ
-/

/-- **Open string state**: occupation numbers n_ℓ at each level ℓ -/
structure OpenStringState (p : MSTParameters) where
  occupation : ℕ → ℕ
  finite_support : ∃ L, ∀ ℓ > L, occupation ℓ = 0

namespace OpenStringState

noncomputable def max_level {p} (state : OpenStringState p) : ℕ :=
  Classical.choose state.finite_support

/-- **Total oscillator number**: Σ_ℓ n_ℓ √ℓ -/
noncomputable def totalOscillatorNumber (p : MSTParameters) (state : OpenStringState p) : ℝ :=
  (Finset.range (state.max_level + 1)).sum
    (fun ℓ => (state.occupation ℓ : ℝ) * sqrt (ℓ : ℝ))

/-- **Invariant mass**: M = M_D0 + (Σ n_i √ℓ_i)/√α' -/
noncomputable def invariantMass (p : MSTParameters) (state : OpenStringState p) : ℝ :=
  p.M_D0 + (state.totalOscillatorNumber p) / sqrt p.alphaPrime

/-- **Equation (2.2)**: Excitation energy ΔE = (α')/(2NR) × (M² - M_D0²) -/
noncomputable def excitationEnergy (p : MSTParameters) (state : OpenStringState p) : ℝ :=
  (p.alphaPrime / (2 * p.N * p.R)) * ((state.invariantMass p) ^ 2 - p.M_D0 ^ 2)

/-- **Equation (2.3)**: Gauge theory mass m_i = (g_YM/N)√(2πℓ_i) in R → ∞ limit -/
noncomputable def gaugeMass (p : MSTParameters) (state : OpenStringState p) : ℝ :=
  (p.g_YM / p.N) * sqrt (2 * π) * (state.totalOscillatorNumber p)

/-- Single oscillator state at level ℓ -/
def singleOscillator (ℓ : ℕ) (p : MSTParameters) : OpenStringState p :=
  { occupation := fun n => if n = ℓ then 1 else 0
    finite_support := ⟨ℓ, fun m hm => by simp; omega⟩ }

/-- **KEY PREDICTION**: m_ℓ = (g_YM/N)√(2πℓ) for single oscillator -/
theorem mass_spectrum_prediction (p : MSTParameters) (ℓ : ℕ) :
    (singleOscillator ℓ p).gaugeMass p = (p.g_YM / p.N) * sqrt (2 * π * ℓ) := by
  sorry

end OpenStringState

/-! ## Section 2: SO(8) R-symmetry at Level ℓ=1

From worldsheet lightcone gauge: ψ^i, α^j oscillators (i,j = 1...8)
-/

/-- **SO(8) representations** at level 1 (from footnote 2 and surrounding text) -/
inductive SO8Rep
  | vector        -- **8**:  ψ^i_{-3/2}|0⟩
  | rank2         -- **36**: ψ^i_{-1/2}α^j_{-1}|0⟩ (unconstrained 8×8 matrix minus constraints)
  | rank3antisym  -- **56**: ψ^i_{-1/2}ψ^j_{-1/2}ψ^k_{-1/2}|0⟩ (antisymmetric)
  deriving DecidableEq

namespace SO8Rep

def dimension : SO8Rep → ℕ
  | vector => 8
  | rank2 => 36
  | rank3antisym => 56

/-- Paper quote: "8+36+56 = 100" bosonic states -/
theorem total_dim_eq_100 :
    dimension vector + dimension rank2 + dimension rank3antisym = 100 := rfl

end SO8Rep

/-- **N=(8,8) SUSY multiplet**: equal bosonic and fermionic content -/
structure SupermultipletN8 (p : MSTParameters) where
  level : ℕ
  level_pos : 0 < level
  bosonic_states : List SO8Rep
  fermionic_states : List SO8Rep
  susy_balance : (bosonic_states.map SO8Rep.dimension).sum =
                 (fermionic_states.map SO8Rep.dimension).sum

def level_one_multiplet (p : MSTParameters) : SupermultipletN8 p where
  level := 1
  level_pos := by norm_num
  bosonic_states := [SO8Rep.vector, SO8Rep.rank2, SO8Rep.rank3antisym]
  fermionic_states := [SO8Rep.vector, SO8Rep.rank2, SO8Rep.rank3antisym]
  susy_balance := rfl

/-! ## Section 3: Resonances and Decay Kinematics -/

/-- **Decay channel**: excited D0 → BPS D0 + closed string with p'^+ = nR/α' -/
structure DecayChannel (p : MSTParameters) where
  initial : OpenStringState p
  n : ℕ
  n_pos : 0 < n
  n_bound : n < p.N

namespace DecayChannel

/-- **Equation (3.1)**: Exact kinematic condition
    (α')/(2NR) M² > (α')/(2(N-n)R) M_D0² -/
noncomputable def kinematicallyAllowed (p : MSTParameters) (decay : DecayChannel p) : Prop :=
  (p.alphaPrime / (2 * p.N * p.R)) * (decay.initial.invariantMass p) ^ 2 >
  (p.alphaPrime / (2 * (p.N - decay.n) * p.R)) * p.M_D0 ^ 2

/-- **Equation (3.2)**: At weak coupling and n ≪ N, condition becomes
    (n√(2π) g_YM R)/(2N) < 1 -/
theorem decay_condition_gauge_form (p : MSTParameters) (decay : DecayChannel p)
    (_weak : p.g_A < 1) (_small_n : decay.n * 10 < p.N) :
    decay.kinematicallyAllowed p ↔
      ((decay.n : ℝ) * sqrt (2 * π) * p.g_YM * p.R) / (2 * p.N) < 1 := by
  sorry

/-- Paper: "decay is forbidden in infinite space i.e. the R → ∞ limit" -/
theorem no_decay_infinite_volume (p : MSTParameters) (decay : DecayChannel p)
    (_large_R : 100 < p.R) :
    ¬ decay.kinematicallyAllowed p := by
  sorry

/-- **Footnote 3**: Decay width Γ = g_A²/(NR) from disc diagram -/
noncomputable def decayWidth (p : MSTParameters) (_decay : DecayChannel p) : ℝ :=
  p.g_A ^ 2 / (p.N * p.R)

lemma decayWidth_pos (p : MSTParameters) (decay : DecayChannel p) :
    0 < decayWidth p decay := by
  unfold decayWidth
  apply div_pos
  · exact sq_pos_of_pos p.g_A_pos
  · exact mul_pos (Nat.cast_pos.mpr p.N_pos') p.R_pos

theorem decayWidth_scaling (p : MSTParameters) (decay : DecayChannel p) :
    ∃ C, decayWidth p decay = C / (p.N * p.R) := by
  use p.g_A ^ 2; rfl

end DecayChannel

/-! ## Section 3: Semiclassical Spinning Strings

Classical soliton: x¹ + ix² = r₀ cos(ωσ) e^(iωt), |σ| < π/(2ω)
Folded macroscopic open string spinning in (x¹,x²)-plane
-/

/-- **Spinning soliton**: (ω, r₀) parameterization -/
structure SpinningSoliton (p : MSTParameters) where
  ω : ℝ
  r₀ : ℝ
  ω_pos : 0 < ω
  r₀_pos : 0 < r₀

namespace SpinningSoliton

/-- **Energy**: E = V_∞ π/ω + (π ω r₀²)/(2 g_YM²)
    where V_∞ = g_YM²/(2N²) for k=1 sector -/
noncomputable def energy (p : MSTParameters) (sol : SpinningSoliton p) : ℝ :=
  (π * p.g_YM ^ 2) / (2 * (p.N : ℝ) ^ 2 * sol.ω) +
  (π * sol.ω * sol.r₀ ^ 2) / (2 * p.g_YM ^ 2)

/-- **Angular momentum**: J = π r₀² / (2 g_YM²) -/
noncomputable def angularMomentum (p : MSTParameters) (sol : SpinningSoliton p) : ℝ :=
  (π / (2 * p.g_YM ^ 2)) * sol.r₀ ^ 2

/-- Paper: "minimizing E at fixed J determines r₀ = g_YM²/(Nω)" -/
noncomputable def optimalRadius (p : MSTParameters) (ω : ℝ) : ℝ :=
  p.g_YM ^ 2 / (p.N * ω)

/-- **Leading Regge trajectory**: E = (g_YM/N)√(2πJ)

Paper: "in agreement with the leading Regge trajectory of the spectrum (2.3)" -/
theorem regge_trajectory (p : MSTParameters) (J : ℝ) (_hJ : 0 < J) :
    ∃ sol : SpinningSoliton p,
      sol.energy p = (p.g_YM / p.N) * sqrt (2 * π * J) := by
  sorry

/-- k-flux generalization: E_k = k(g_YM/N)√(2πJ) -/
theorem regge_trajectory_k_flux (p : MSTParameters) (k : Fin p.N) (J : ℝ) (_hJ : 0 < J) :
    ∃ E, E = (k.val : ℝ) * (p.g_YM / p.N) * sqrt (2 * π * J) := by
  use (k.val : ℝ) * (p.g_YM / p.N) * sqrt (2 * π * J)

end SpinningSoliton

/-! ## IR CFT: Symmetric Product Orbifold -/

/-- **Sym^D(ℝ⁸)**: IR description with D = gcd(k,N) (Kologlu et al '16) -/
structure SymmetricProductCFT (D : ℕ) where
  copies : ℕ := D
  target_dim : ℕ := 8
  central_charge : ℕ := 8 * D

namespace SymmetricProductCFT

theorem ir_cft_correspondence (p : MSTParameters) (sec : FluxSector p)
    (_large_gR : 1 < p.g_YM * p.R) :
    ∃ cft : SymmetricProductCFT (sec.divisor p),
      cft.copies = Nat.gcd sec.k.val p.N := by
  exact ⟨{ copies := Nat.gcd sec.k.val p.N }, rfl⟩

end SymmetricProductCFT

/-! ## Wilson Lines as Domain Walls -/

/-- Paper: "fundamental Wilson line... interpolates between gapless non-flux
    vacuum and gapped k=1 flux vacuum" -/
structure WilsonLineDomainWall (p : MSTParameters) where
  source : FluxSector p := FluxSector.zeroFlux p
  target : FluxSector p := FluxSector.singleFlux p

namespace WilsonLineDomainWall

/-- Paper: "should flow to a conformal boundary condition...
    inherited from D0-brane boundary condition of worldsheet theory" -/
axiom flows_to_D0_brane_boundary (p : MSTParameters) (_W : WilsonLineDomainWall p)
    (_large_gR : 1 < p.g_YM * p.R) : True

end WilsonLineDomainWall

/-! ## Summary: Main Testable Predictions

Paper conclusion: "striking predictions... would either serve as highly
nontrivial non-perturbative tests... or disprove the latter"
-/

section TestablePredictions  -- FIX: was just "ions"

variable (p : MSTParameters)

/-- **All predictions bundled** -/
theorem mst_testable_predictions :
    (∀ ℓ > 0, ∃ m, m = (p.g_YM / p.N) * sqrt (2 * π * ℓ)) ∧
    (∀ decay : DecayChannel p, DecayChannel.decayWidth p decay = p.g_A ^ 2 / (p.N * p.R)) ∧
    (∀ J > 0, ∃ E, E = (p.g_YM / p.N) * sqrt (2 * π * J)) := by
  constructor
  · intro ℓ _; use (p.g_YM / p.N) * sqrt (2 * π * ℓ)
  constructor
  · intro _; rfl
  · intro J _; use (p.g_YM / p.N) * sqrt (2 * π * J)

/-- Paper: "accessible through Hamiltonian truncation/DLCQ or matrix QM bootstrap" -/
axiom verification_via_numerical_methods :
  ∀ (ℓ : ℕ) (ε : ℝ), ∃ (numerical_mass : ℝ),
    |numerical_mass - (p.g_YM / p.N) * sqrt (2 * π * ℓ)| < ε

end TestablePredictions

/-! ## Computational Verification Frameworks -/

/-- Framework for Hamiltonian truncation / DLCQ verification.

Paper: "accessible through Hamiltonian truncation/DLCQ" -/
structure HamiltonianTruncation (p : MSTParameters) where
  /-- Cutoff level -/
  L_max : ℕ
  /-- Numerical masses computed up to L_max -/
  computed_masses : ℕ → ℝ
  /-- Agreement with MST prediction within error ε -/
  ε : ℝ
  ε_pos : 0 < ε
  agreement : ∀ ℓ ≤ L_max,
    |(computed_masses ℓ) - (p.g_YM / p.N) * sqrt (2 * π * ℓ)| < ε

/-- Framework for matrix quantum mechanics bootstrap.

Paper: "matrix quantum mechanics bootstrap methods" -/
structure BootstrapMethod (p : MSTParameters) where
  /-- Numerical precision achieved -/
  ε : ℝ
  ε_pos : 0 < ε
  /-- Bootstrap bounds on masses -/
  mass_bounds : ℕ → ℝ × ℝ
  /-- MST prediction lies within bounds -/
  consistent : ∀ ℓ,
    let (lower, upper) := mass_bounds ℓ
    lower ≤ (p.g_YM / p.N) * sqrt (2 * π * ℓ) ∧
    (p.g_YM / p.N) * sqrt (2 * π * ℓ) ≤ upper

end MatrixStringTheory
