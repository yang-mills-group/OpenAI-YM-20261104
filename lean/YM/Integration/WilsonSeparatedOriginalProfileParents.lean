import YM.Integration.WilsonSeparatedOriginalReplicaSupport

/-! Complete three-source parent sum on the actual original torus with a finite period-independent price. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalProfileParents
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Extra.Histories Push Local Marker
open MergeProof Accent Menu RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Records
open RG05Readout.Native RG05Readout.View GridApprox.Nil WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open PhysicalNext.Repeat.Legato WilsonAllDateHarvestObservedReplay RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Flatten
open WilsonSeparatedOriginalReplicaScanner WilsonSeparatedOriginalProfilePortfolio WilsonSeparatedOriginalPairedFolio
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n t N per:ℕ}
variable (s:Fin 3→ℕ)(S:(i:Fin 3)→Emblems R.family (s i))(x:(i:Fin 3)→Palette R.family (s i))
variable (P:(o:Fin 3 → Site (R.family.side n per))→(i:Fin 3)→Sight R.family (s i) per)(roster:(Fin 3 → Site (R.family.side n per)) → Census (Fin 3))
    (full:∀o,univ∈(roster o).choices)(nt:n<t)(tN:t≤N)

def whole (r:ℝ)(Ψ:Wave (Fin 3))(m:ℕ)(g:Body)(V:Config G (R.family.side n per)):ℂ:=
  premiums R.family s m n r * ∑o:Fin 3 → Site (R.family.side n per),physical R o s S x nt tN r Ψ g V

theorem original (d k:ℕ)(Q fee:ℝ)(ep:0≤fee)
    {r η X cap:ℝ}(rp:0<r)(room:r≤R.family.S.a n)(sep:0<η)(small:η≤1)
    (Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0≤X)(capX:Tall Ψ (rank+1) 1 X)
    (cp:0≤cap)(shape:∀y∈tsupport Ψ.val,∀i:Fin 3,‖y i‖≤cap)
    (buying:∀o∈Pulse.area (C:=R.family) (p:=per) (b:=n) ⌈cap+2⌉₊,
      ∀f:Fin 3→Body,(∀i,Tall (f i) (s i+2) 1 1) → buy R.family n per o (r*η/2) f →
      Captured o (fun _=>(1,false)) s (fun z=>f z.val.1) R.makes (P o) S x (roster o) nt.le tN d k Q fee):
    let admit:=fun o=>allowed R o s S x (P o) (roster o) (full o) nt tN r η fee
    let sale:=fun o=>WilsonSeparatedOriginalProfileColumn.Posted R o s S x (P o) (roster o) (full o) nt tN fee
    let quota:=earn s R.family n rank η r*X
    let A:=Pulse.area (C:=R.family) (p:=per) (b:=n) (V:=Fin 3) ⌈cap+2⌉₊
    ∃L:(o:Fin 3 → Site (R.family.side n per))→List (Entry s (admit o) (sale o)),(∀o,o∉A → L o=[]) ∧
      (∀o∈A,((L o).map Entry.rent).sum≤quota) ∧
      ∀(m:ℕ)(g:Body)(V:Config G (R.family.side n per)),flags (R.family.path.rep N per n).p.threshold V=∅ →
        ‖whole R s S x nt tN r Ψ m g V-premiums R.family s m n r*∑o:Fin 3 → Site (R.family.side n per),received g (L o) V‖≤
          ‖premiums R.family s m n r‖*((((Lattice.box ⌈cap+2⌉₊).card:ℝ)^3)*(mass g*(abs quota)*fee)):=by
  classical
  intro admit sale quota A
  have source (o:Fin 3 → Site (R.family.side n per))(live:o∈A):∃L:List (Entry s (admit o) (sale o)),(L.map Entry.rent).sum≤quota ∧
      ∀(g:Body)(V:Config G (R.family.side n per)),flags (R.family.path.rep N per n).p.threshold V=∅ →
      ‖physical R o s S x nt tN r Ψ g V-received g L V‖ ≤ mass g*quota*fee:=
    WilsonSeparatedOriginalProfilePortfolio.original R o s S x (P o) (roster o) (full o) nt tN d k Q fee ep rp room sep small Ψ rank grade scatter xp capX (buying o live)
  let L (o:Fin 3 → Site (R.family.side n per)):List (Entry s (admit o) (sale o)):=if h:o∈A then (source o h).choose else []
  have empty (o:Fin 3 → Site (R.family.side n per))(h:o∉A):L o=[]:=dif_neg h
  have grant (o:Fin 3 → Site (R.family.side n per))(h:o∈A):L o=(source o h).choose:=dif_pos h
  refine ⟨L,empty,fun o h=>by rw [grant o h];exact (source o h).choose_spec.1,?_⟩
  intro m g V clean
  let column (o:Fin 3 → Site (R.family.side n per)):ℂ:=physical R o s S x nt tN r Ψ g V-received g (L o) V
  have outside (o:Fin 3 → Site (R.family.side n per))(h:o∉A):column o=0:=by
    have z:=WilsonSeparatedOriginalReplicaSupport.zero R s (fun i=>Launch (m:=t) s S x i N) (nt.le.trans tN) (nt.trans_le tN) rp Ψ shape _ o h (WilsonSeparatedOriginalReplicaSupport.radius R.family n cp room) g V
    unfold column physical;rw [z,empty o h];simp [received]
  have reduce:∑o:Fin 3 → Site (R.family.side n per),column o=∑o∈A,column o:=(sum_subset (subset_univ A) (fun o _ h=>outside o h)).symm
  have bound (o:Fin 3 → Site (R.family.side n per))(h:o∈A):‖column o‖ ≤ mass g*(abs quota)*fee:=by
    unfold column;rw [grant o h];exact ((source o h).choose_spec.2 g V clean).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (positive g)) ep)
  have paid:‖∑o∈A,column o‖≤(A.card:ℝ)*(mass g*(abs quota)*fee):=calc
    _≤∑o∈A,‖column o‖:=norm_sum_le ..
    _≤∑_o∈A,mass g*(abs quota)*fee:=sum_le_sum bound
    _=_:=by simp only [sum_const,nsmul_eq_mul]
  have card:(A.card:ℝ)≤((Lattice.box ⌈cap+2⌉₊).card:ℝ)^3:=by
    exact_mod_cast (show A.card≤(Lattice.box ⌈cap+2⌉₊).card^3 by simpa only [Fintype.card_fin] using Pulse.area_cost (C:=R.family) (p:=per) (b:=n) (V:=Fin 3) ⌈cap+2⌉₊)
  unfold whole;rw [←mul_sub,←sum_sub_distrib,show (∑o:Fin 3 → Site (R.family.side n per),(physical R o s S x nt tN r Ψ g V-received g (L o) V))=∑o:Fin 3 → Site (R.family.side n per),column o from rfl,reduce,norm_mul]
  exact mul_le_mul_of_nonneg_left (paid.trans (mul_le_mul_of_nonneg_right card (mul_nonneg (mul_nonneg (positive g) (abs_nonneg _)) ep))) (norm_nonneg _)

end YM.Integration.WilsonSeparatedOriginalProfileParents
