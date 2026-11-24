import YM.Integration.WilsonSeparatedOriginalSlabFolio
import YM.Integration.WilsonSeparatedOriginalProfileTariff

/-! The complete uncentered physical parent array. The price counts true occupied parents before the ultraviolet period. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabAtlas
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extraction RG05Readout
open RG05Readout.Native RG05Readout.Pulse RG05Readout.Address RG05Readout.Nuclear PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalPairedFolio WilsonSeparatedOriginalSlabFolio
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n N per:ℕ}(s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette R.family (s i))(top:n ≤ N)
variable {T:Type*}(age:T → ℕ)(opened:∀a,age a+1 ≤ N)(hold:(a:T) → Config G (R.family.side (age a) per))
local notation "Origins"=>Fin 3 → Site (R.family.side n per)

def whole (r:ℝ)(Ψ:Wave (Fin 3))(m:ℕ)(g:Body)(a:T):ℂ:=
  premiums R.family s m n r*∑o:Origins,amount R s v o top age opened hold Ψ r g a

theorem original (book:Origins → (Fin 3 → Body) → (T → ℂ) → Prop){ε r η X cap:ℝ}(ep:0 ≤ ε)
    (rp:0<r)(room:r ≤ R.family.S.a n)(sep:0<η)(small:η ≤ 1)(Ψ:Wave (Fin 3))(rank:ℕ)
    (grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0 ≤ X)(sizeX:Tall Ψ (rank+1) 1 X)(cp:0 ≤ cap)
    (shape:∀x∈tsupport Ψ.val,∀i:Fin 3,‖x i‖ ≤ cap)
    (bought:∀o∈Pulse.area (C:=R.family) (p:=per) (b:=n) ⌈cap+2⌉₊,∀f,allowed R s o r η f →
      ∃A,settled R s v o top age opened hold (book o) ε f A):
    let admit:=fun o=>allowed R s o r η
    let sale:=fun o=>settled R s v o top age opened hold (book o) ε
    let quota:=earn s R.family n rank η r*X
    let A:=Pulse.area (C:=R.family) (p:=per) (b:=n) (V:=Fin 3) ⌈cap+2⌉₊
    ∃L:(o:Origins) → List (Entry s (admit o) (sale o)),(∀o,o∉A → L o=[]) ∧
      (∀o∈A,((L o).map Entry.rent).sum ≤ quota) ∧ ∀(m:ℕ)(g:Body)(a:T),
        ‖whole R s v top age opened hold r Ψ m g a-premiums R.family s m n r*∑o:Origins,received g (L o) a‖ ≤
          ‖premiums R.family s m n r‖*((((Lattice.box ⌈cap+2⌉₊).card:ℝ)^3)*(mass g*abs quota*ε)):=by
  classical
  intro admit sale quota A
  have source (o:Origins)(live:o∈A):∃L:List (Entry s (admit o) (sale o)),(L.map Entry.rent).sum ≤ quota∧
      ∀(g:Body)(a:T),‖amount R s v o top age opened hold Ψ r g a-received g L a‖ ≤ mass g*quota*ε:=
    WilsonSeparatedOriginalSlabFolio.original R s v o top age opened hold (book o) ep rp room sep small Ψ rank grade scatter xp sizeX (bought o live)
  let L (o:Origins):List (Entry s (admit o) (sale o)):=if h:o∈A then (source o h).choose else []
  have grant (o:Origins)(h:o∈A):L o=(source o h).choose:=dif_pos h
  have empty (o:Origins)(h:o∉A):L o=[]:=dif_neg h
  refine ⟨L,empty,fun o h=>by rw [grant o h];exact (source o h).choose_spec.1,?_⟩
  intro m g a
  let column (o:Origins):ℂ:=amount R s v o top age opened hold Ψ r g a-received g (L o) a
  have outside (o:Origins)(h:o∉A):column o=0:=by
    have z:amount R s v o top age opened hold Ψ r g a=0:=by
      unfold amount
      rw [setIntegral_congr_fun (g:=fun _=>0) Pert.Cellular.cells_compact.measurableSet (fun z hz=>by
        rw [WilsonSeparatedOriginalSlabWave.absent R s v o top (opened a) (hold a) rp Ψ shape _ h
          (WilsonSeparatedOriginalReplicaSupport.radius R.family n cp room) z hz,mul_zero]),integral_zero]
    unfold column;rw [z,empty o h];simp [received]
  have reduce:∑o:Origins,column o=∑o∈A,column o:=(sum_subset (subset_univ A) (fun o _ h=>outside o h)).symm
  have bound (o:Origins)(h:o∈A):‖column o‖ ≤ mass g*(abs quota)*ε:=by
    unfold column;rw [grant o h];exact ((source o h).choose_spec.2 g a).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (positive g)) ep)
  have paid:‖∑o∈A,column o‖ ≤ (A.card:ℝ)*(mass g*(abs quota)*ε):=calc
    _ ≤ ∑o∈A,‖column o‖:=norm_sum_le ..
    _ ≤ ∑_o∈A,mass g*(abs quota)*ε:=sum_le_sum bound
    _ = _:=by simp only [sum_const,nsmul_eq_mul]
  have card:(A.card:ℝ) ≤ ((Lattice.box ⌈cap+2⌉₊).card:ℝ)^3:=by
    exact_mod_cast (show A.card ≤ (Lattice.box ⌈cap+2⌉₊).card^3 by simpa only [Fintype.card_fin] using Pulse.area_cost (C:=R.family) (p:=per) (b:=n) (V:=Fin 3) ⌈cap+2⌉₊)
  unfold whole;rw [←mul_sub,←sum_sub_distrib,show (∑o:Origins,(amount R s v o top age opened hold Ψ r g a-received g (L o) a))=∑o:Origins,column o from rfl,reduce,norm_mul]
  exact mul_le_mul_of_nonneg_left (paid.trans (mul_le_mul_of_nonneg_right card (mul_nonneg (mul_nonneg (positive g) (abs_nonneg _)) ep))) (norm_nonneg _)

end YM.Integration.WilsonSeparatedOriginalSlabAtlas
