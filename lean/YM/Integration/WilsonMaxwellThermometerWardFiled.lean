import YM.Integration.WilsonMaxwellThermometerWardFaces

/-! Before any continuum passage the pole-zero and pole-two part of the true
filed grade-six source is a linear read of its ungraded all-fields value.
The odd pole-three contributes zero in every even lower face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardFiled
open Function Filter Set Finset MeasureTheory Lattice Labels Source Wilson PertExtension PertExtension.Orb
open PertExtension.Series Chart Series.Radial Series.Tested WilsonMaxwellThermometerWardPupil
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {n:Side}

def reading (g:ℝ) (q:ℕ) (K f:Config G n→ℝ) :=
  f 1 * diagonalWith (tray G) (restrictedO K) q +
  g^2 * diagonalWith (tray G) (restrictedO ((f-(fun _=>f 1))*K)) (2+q)

theorem added {f b:Config G n→ℝ} (even:Even n.val) (hf:PreTest f) (hb:PreTest b) :
    diagonalWith (tray G) (restrictedO (f+b)) =
      diagonalWith (tray G) (restrictedO f)+diagonalWith (tray G) (restrictedO b):=by
  have hab:PreTest (f+b):=⟨fun u hu U=>by simp only [Pi.add_apply,hf.gauge u hu U,hb.gauge u hu U],
    ⟨hf.curved.boundedness.add hb.curved.boundedness,hf.curved.germ.add hb.curved.germ⟩,hf.continuous.add hb.continuous⟩
  apply (before_tree_formula even (traySpec G) hab).unique
  rw [WilsonMaxwellThermometerWardCoefficient.addition f b hf.continuous hb.continuous]
  exact (before_tree_formula even (traySpec G) hf).add (before_tree_formula even (traySpec G) hb)

variable {d:ℕ} {F:Frame G d} (C:SectionData F) (c:F.Coeff) (L:ℂ→L[ℝ]ℝ)
    (o:Site n) {H:Hol G} (sound:C.Sound H) (pop:Bid.pop C)
local notation "head" => selected C c L o (next (F:=F))
local notation "high" => selected C c L o (later (F:=F))
local notation "raw" => selected C c L o (active (F:=F))
local notation "panel" => (fun U:Config G n=>L (C.places c o U))

include sound pop in
theorem original (even:Even n.val) (simple:G.Simple) (g:ℝ) {q:ℕ} (parity:Even q) {K:Config G n→ℝ}
    (hk:PreTest K) (order:RadialOrder q (fun x:Dir G n=>K (representative x))):
    reading g q K panel =
      L (c 0) * diagonalWith (tray G) (restrictedO K) q +
      g^2 * diagonalWith (tray G) (restrictedO (head*K)) (2+q) +
      g^3 * diagonalWith (tray G) (restrictedO (high*K)) (3+q) := by
  have here:=WilsonMaxwellThermometerWardCoefficient.admitted C c L o sound pop
  obtain ⟨second,third⟩:=costs C c L o sound pop simple
  have smooth:ContDiffAt ℝ ∞ (fun x:Dir G n=>raw (representative x)) 0:=(here active).curved.germ
  have low:jet (fun x:Dir G n=>raw (representative x)) 0=0:=jets_vanish smooth second (by decide)
  have origin:raw 1=0 := by
    have h0:=congrFun low (0:Dir G n)
    rw [jet_zero,representative_zero] at h0
    exact h0
  have closed:panel 1=L (c 0) := by
    change L (C.places c o 1)=L (c 0)
    rw [literal C c L o sound,origin,add_zero]
  have net:(panel - fun _=>panel 1)=raw:=by
    funext U
    rw [Pi.sub_apply,literal C c L o sound,closed]
    ring
  have split:raw*K=head*K+high*K:=by
    rw [show raw=head+high from funext (WilsonMaxwellThermometerWardPupil.split C c L o simple),add_mul]
  have hd:=WilsonMaxwellThermometerWardCompanion.multiply (here next) hk
  have hh:=WilsonMaxwellThermometerWardCompanion.multiply (here later) hk
  have gone:=diag_down (traySpec G) hh.curved (fun u=>bill_mul (third u) (order u)) even (2+q) (by omega)
  have odd:Odd (3+q):=by obtain ⟨a,ha⟩:=parity; exact ⟨1+a,by omega⟩
  unfold reading
  rw [net,closed,split,added even hd hh,Pi.add_apply,gone,add_zero,
    Orb.normalized_odd (traySpec G) even _ odd,mul_zero,add_zero]

end YM.Integration.WilsonMaxwellThermometerWardFiled
