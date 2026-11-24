import YM.Integration.WilsonMaxwellThermometerWardOccupant

/-! A cleared genuine spectator retains its ordinary conditional coefficient
under the radial projection of the upper equation. Pay the spectator at its
own vanishing order before dropping the pole-three and higher upper rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardCompanion
open Function Filter Set Finset MeasureTheory Lattice Labels Source Wilson PertExtension PertExtension.Orb
open PertExtension.Series Chart Series.Radial Series.Tested WilsonMaxwellThermometerWardPupil
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {n:Side}

theorem multiply {f g:Config G n→ℝ} (hf:PreTest f) (hg:PreTest g) : PreTest (f*g) :=
  ⟨fun u hu U=>by simp only [Pi.mul_apply,hf.gauge u hu U,hg.gauge u hu U],
    ⟨hf.curved.boundedness.mul hg.curved.boundedness,hf.curved.germ.mul hg.curved.germ⟩,hf.continuous.mul hg.continuous⟩

variable {d:ℕ} {F:Frame G d} (C:SectionData F) (c:F.Coeff) (L:ℂ→L[ℝ]ℝ)
    (o:Site n) {H:Hol G} (sound:C.Sound H) (pop:Bid.pop C)
local notation "head" => selected C c L o (next (F:=F))
local notation "high" => selected C c L o (later (F:=F))
local notation "raw" => selected C c L o (active (F:=F))

include sound pop in
theorem coefficient (even:Even n.val) (simple:G.Simple) {q:ℕ} {K:Config G n→ℝ}
    (hk:PreTest K) (order:RadialOrder q (fun x:Dir G n=>K (representative x)))
    (heard:∀t:ℝ,t≠0→preExpectation (raw*K) t=0) :
    diagonalWith (tray G) (restrictedO (head*K)) (2+q)=0 :=by
  have admitted:=WilsonMaxwellThermometerWardCoefficient.admitted C c L o sound pop
  have hr:=multiply (admitted active) hk
  have hh:=multiply (admitted next) hk
  have hl:=multiply (admitted later) hk
  have ⟨ar,al⟩:=costs C c L o sound pop simple
  have dr:=diag_down (traySpec G) hr.curved (fun u=>bill_mul (ar u) (order u)) even
  have dl:=diag_down (traySpec G) hl.curved (fun u=>bill_mul (al u) (order u)) even
  have series:=before_tree_formula even (traySpec G) hr
  have split:raw*K=head*K+high*K:=by
    rw [show raw=head+high from funext (WilsonMaxwellThermometerWardPupil.split C c L o simple),add_mul]
  have added:=WilsonMaxwellThermometerWardCoefficient.addition (head*K) (high*K) hh.continuous hl.continuous
  have coefficients:diagonalWith (tray G) (restrictedO (raw*K))=
      diagonalWith (tray G) (restrictedO (head*K))+diagonalWith (tray G) (restrictedO (high*K)):=by
    apply series.unique
    rw [split,added]
    exact (before_tree_formula even (traySpec G) hh).add (before_tree_formula even (traySpec G) hl)
  have same:diagonalWith (tray G) (restrictedO (raw*K)) (2+q)=diagonalWith (tray G) (restrictedO (head*K)) (2+q):=by
    simpa only [Pi.add_apply,dl (2+q) (by omega),add_zero] using congrFun coefficients (2+q)
  have first:(Tendsto (fun t:ℝ=>t⁻¹^(2+q)*preExpectation (raw*K) t) Tested.germ
      (𝓝 (diagonalWith (tray G) (restrictedO (head*K)) (2+q)))):= by
    simpa only [Nat.add_zero,smul_eq_mul,same] using (series.shift dr).tendsto_first
  have zero:(fun t:ℝ=>t⁻¹^(2+q)*preExpectation (raw*K) t)=ᶠ[Tested.germ] fun _=> 0 := by
    filter_upwards [eventually_pos] with t ht
    simp only [heard t ht.ne',mul_zero]
  exact tendsto_nhds_unique first (tendsto_const_nhds.congr' zero.symm)

end YM.Integration.WilsonMaxwellThermometerWardCompanion
