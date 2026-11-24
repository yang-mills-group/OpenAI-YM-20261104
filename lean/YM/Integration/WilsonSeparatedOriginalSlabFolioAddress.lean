import YM.Integration.WilsonSeparatedOriginalPairedFolio
import YM.Integration.WilsonSeparatedOriginalSlabDriven

/-! The actual signed center weight of each original nuclear leaf is an addressed test functional on every Body.  Relative child offsets stay in its independently issued physical product. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFolioAddress
open Function Finset Set MeasureTheory RG Lattice Wilson Source RG05Readout RG05Readout.Native RG05Readout.Nuclear
open WilsonSeparatedOriginalPairedFolio WilsonSeparatedOriginalSlabDriven
open scoped BigOperators Classical Topology ContDiff
variable {X:Type*}{s:Fin 3→ℕ}{allow:(Fin 3→Body)→Prop}{book:(Fin 3→Body)→(X→ℂ)→Prop}
local notation "Leaf"=>Entry s allow book

private theorem integrable (e:Leaf)(g:Body):IntegrableOn (fun z=>g.val z*e.alpha z) Native.box:=
   (show ContDiff ℝ ∞ g.val from g.2).continuous.continuousOn.mul e.smooth|>.integrableOn_compact Pert.Cellular.cells_compact

def reading (e:Leaf):PulseC where
  toFun g:=ink g e
  map_add' f g:=by
    change (∫z in Native.box,(f.val z+g.val z)*e.alpha z)=_
    simp_rw [add_mul];exact integral_add (integrable e f) (integrable e g)
  map_smul' c g:=by
    change (∫z in Native.box,(c*g.val z)*e.alpha z)=c*_
    simp_rw [mul_assoc];exact integral_const_mul c _

def price (e:Leaf):ℝ:=tariff*e.rent

theorem nonneg (e:Leaf):0≤price e:=mul_nonneg positive.le e.pos

theorem charged (e:Leaf)(H:ℕ):Priced H (reading e) (price e):=by
  intro g c hc
  change ‖ink g e‖≤price e*c
  have h:‖∫z in Native.box,g.val z*e.alpha z‖ ≤ (c*e.rent)*volume.real Native.box:=by
    apply norm_setIntegral_le_of_norm_le_const Pert.Cellular.cells_compact.measure_lt_top
    intro z hz
    rw [norm_mul];apply mul_le_mul _ (e.cap z hz) (norm_nonneg _) hc.nonneg
    simpa only [norm_iteratedFDeriv_zero] using hc 0 (Nat.zero_le _) z hz
  unfold price tariff ink
  calc _ ≤ _ := h
       _ ≤ (c*e.rent)*(1+volume.real Native.box):=mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (mul_nonneg hc.nonneg e.pos)
       _ = _ :=by ring

def stamp (e:Leaf):PulseC:=(price e:ℂ)⁻¹ • reading e

theorem issued (e:Leaf)(H:ℕ):Priced H (stamp e) 1:=by
  intro g c hc
  change ‖(price e:ℂ)⁻¹*reading e g‖≤1*c
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (nonneg e),one_mul]
  by_cases h:price e=0
  · simpa [h] using hc.nonneg
  · exact (inv_mul_le_iff₀ (lt_of_le_of_ne (nonneg e) (Ne.symm h))).mpr (charged e H g c hc)

theorem restores (e:Leaf)(g:Body):(price e:ℂ)*stamp e g=ink g e:=by
  change (price e:ℂ)*((price e:ℂ)⁻¹*ink g e)=ink g e
  by_cases h:e.rent=0
  · have z:ink g e=0:=norm_le_zero_iff.mp (by simpa only [h,mul_zero] using cost g e)
    simp [z]
  · have hp:0<price e:=mul_pos positive (lt_of_le_of_ne e.pos (Ne.symm h))
    rw [←mul_assoc,mul_inv_cancel₀ (by exact_mod_cast hp.ne'),one_mul]

theorem ledger (L:List Leaf):(L.map price).sum=tariff*(L.map Entry.rent).sum:=by
  induction L with
  | nil=>simp
  | cons e l ih=>simp only [List.map_cons,List.sum_cons,mul_add,ih,price]

end YM.Integration.WilsonSeparatedOriginalSlabFolioAddress
