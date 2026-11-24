import YM.MS.Menus.Glyph
import YM.MS.Theater.DataK
import YM.Next.MAXWELL.Algebra
import YM.Next.MAXWELL.Covariance

set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge} {h k r:ℕ} {u:ℤ} {X:Law G} {B:Physical.Deck G} {p:Pol G}
lemma limitH (hP:At p (k,r)): p∈Labels.limited G k:= by
    apply ( MvPolynomial.mem_restrictSupport_iff ℂ ).mpr; intro j hj; replace hj:= MvPolynomial.mem_support_iff.mp hj; obtain hv := nodeId _ _ |>.mp hP hj; change height j≤ k; rw [ Labels.weight_slot ] at hv; exact le_of_eq (congr_arg Prod.fst hv)
lemma bipFire (hP:At p (k,r))(he:p≠0): r≤k:= by obtain ⟨v,hv⟩:= MvPolynomial.exists_coeff_ne_zero he; obtain ht:= ( nodeId _ _ |>.mp hP ) hv; obtain hc := Labels.power_le v; rw [ht] at hc; rw [ Labels.weight_slot ] at ht; obtain hx := Prod.ext_iff.mp ht|>.1; rwa [ show k=height v from Eq.symm hx ]
variable (B)
def Indigo (h r:ℕ): Module.Basis (B.BIndex h r) ℝ (IvSpace G h r):=(Module.finBasis ℝ _).map (Studio B h r)
variable {d:ℕ}
def Letters (B:Deck G)(p:Glyph B d): WickPol G:= reduceEq (film B p.2.2 ( h:=p.1.val ) ( r:=p.2.1.val ) ) -- d implicit variable error
variable {i:Glyph B h}
lemma letS (i:Fin (d+1))(j: Fin (i.val+1))(k: B.BIndex i.val j.val) : Letters B ⟨i,j,k⟩=( Indigo B i.val j.val k ).val:= Eq.trans (sees B k ) (congr_arg Subtype.val (Module.Basis.map_apply ..|>.symm)) -- ∃
def ΕData (B:Deck G)(p:Glyph B h): Labels.Pol G:= film B p.2.2 ( h:=p.1.val ) ( r:=p.2.1.val )
lemma filmBasic (p:Glyph B h): ΕData B p∈ Film0 G p.1.val p.2.1.val:= filmW B p.2.2
lemma letter_sector (i: Glyph B d): Letters B i∈shellSector G i.1.val:= by
   obtain he:=filmBasic B i; let p:=ΕData B i; exact ⟨ ⟨ p,limitH he.2, (( cinema (ΕData B i) ).mp he).2.1⟩,rfl⟩
lemma indoor (i: Glyph B d): Letters B i∈ shellSector G d:= Free.chain ( l:=d ) ( Nat.le_of_lt_succ i.1.isLt ) ( letter_sector B i ) -- names
lemma real_shell (i:Glyph B d): Free.realForm ( Letters B i )=Letters B i:= by
    obtain h:=filmBasic B i; apply Maxwell.equalPol; intro A; rw [Free.real_eval]; unfold Letters; rw [ jet_value ]; exact Eq.trans ( conj_value ( ΕData B i ) _|>.symm ) ( congr_arg _ ( ( cinema ( ΕData B i ) ).mp h|>.2.2 ) ) -- ℝ
abbrev biasW (G:Gauge) (i:ℕ×ℕ) := MvPolynomial.weightedHomogeneousComponent (R:=ℂ) (fun a: Maxwell.Slot G => ( a.1+2,(1:ℕ) ) ) i -- syntax
lemma bias_C (i:Glyph B d)(u:ℕ×ℕ): biasW G u ( Letters B i )=if u=(i.1.val,i.2.1.val) then Letters B i else 0:= by
    obtain H:= nodeId _ _ |>.mp ( ( filmBasic B i ).2 );
    let P:= ΕData B i; change biasW G u ( reduceEq P )=_; rw [show biasW G u ( reduceEq P )= reduceEq ( piece ( G:=G ) u P ) from ( Free.commuting Labels.bidegree _ reduceEq ( Free.reduce_grade fun i=> ( i+2,(1:ℕ) ) ) P u ) ]; split; · next he=> subst u; rw [piece, H.weightedHomogeneousComponent_same ]; rfl
    next hx=> rw [piece, H.weightedHomogeneousComponent_ne u hx,map_zero]
def policy (d:ℕ): Submodule ℂ (WickPol G):= Submodule.span ℂ (Set.range ( Letters B (d:=d) ))
private lemma cling (t:ℝ)(X:WickPol G): (↑t:ℂ) • X=t • X:= IsScalarTower.algebraMap_smul ℂ t _
lemma via {v:WickPol G}(hT:h≤d)(hv: r≤h)(hp:v∈ IvSpace G h r): v∈ policy B d:= by
   let U: IvSpace G h r:=⟨ v,hp⟩; let X:= Indigo B h r; let i : Fin ( d+1 ):= ⟨ h,by omega⟩; let j : Fin (h+1):=⟨r,by omega⟩; suffices he : ( ∑ k,X.repr U k • X k ).val ∈ policy B d by rw [ X.sum_repr ] at he; exact he
   rw [AddSubmonoidClass.coe_finsetSum]; exact sum_mem fun k _=> by rw [Submodule.coe_smul, ← cling ]; exact ( show ( ( X.repr U k:ℝ ):ℂ) • (X k).val∈ policy B d from smul_mem _ _ (subset_span (show ( X k ).val∈ Set.range (Letters B ( d:=d )) from ⟨ ⟨ i,j,k⟩,letS .. ⟩ )) )
lemma cover_all (d:ℕ): policy B d=shellSector G d:= by
    refine le_antisymm ( Submodule.span_le.mpr ( Set.range_subset_iff.mpr ( indoor B ) ) ) ?_; -- check range
    rintro p ⟨v,rfl⟩; suffices ht: span ℂ (pureReal G d )≤Submodule.comap (observable G d) ( policy B d ) from ht ( pure_real_span (G:=G) Submodule.mem_top );
    rw [ Submodule.span_le ]; rintro t ⟨he,i,h,hv⟩; have hp : t.val∈ Film0 G i.1 i.2:= by apply ( cinema _ ).mpr; exact ⟨ ( pure_grade i _ ).1 hv,t.property.2, congr_arg Subtype.val he ⟩
    by_cases hQ:t.val=0; · change reduceEq t.val∈ policy B d; rw [hQ,map_zero]; exact zero_mem _
    apply via B h ( bipFire hp.2 hQ ); exact ⟨ ⟨ t.val,hp ⟩,rfl⟩ -- τ target inference
lemma sumKn (i: Fin (h+1))(j: Fin (i.val+1))(X: Glyph B h→ ℝ): ( ∑ k:Glyph B h, if (i.val,j.val)=( k.1.val,k.2.1.val ) then X k • Letters B k else 0 )= (∑ t, X ⟨ i,j,t ⟩ • ( Indigo B i.val j.val t ).val):= by
   classical
   -- sum_sigma.Div. induction simpler sigma sum narrow.
   rw [ Fintype.sum_sigma ]; rw [ Finset.sum_eq_single_of_mem i (Finset.mem_univ _) ];
   · rw [ Fintype.sum_sigma ]; rw [ Finset.sum_eq_single_of_mem j ( Finset.mem_univ _) ]; · exact Finset.sum_congr rfl fun k _=> Eq.trans (if_pos rfl) (congr_arg ( X ⟨ i,j,k ⟩ • · ) ( letS .. ))
     intro x hx ht; apply Finset.sum_eq_zero; intro y _; exact if_neg (fun he=> ht (Fin.ext (Prod.ext_iff.mp he|>.2.symm)))
   intro a ha hv; apply Finset.sum_eq_zero; intro j _; exact if_neg (fun ht=> hv ( Fin.ext (Prod.ext_iff.mp ht|>.1.symm)))
lemma indR (h:ℕ): LinearIndependent ℝ (Letters B ( d:=h )):= by
   apply Fintype.linearIndependent_iff.mpr; intro X hx z; rcases z with ⟨i,j,k⟩; let M:= biasW G ( i.val,j.val ); obtain hu:= congr_arg (fun x=> M.restrictScalars ℝ x) hx; simp_rw [ map_sum,map_smul,map_zero ] at hu; let T:= Indigo B i.val j.val; have he : ∑ k, X ⟨ i,j,k ⟩ • T k=0:= by
       apply Subtype.ext; rw [ AddSubmonoidClass.coe_finsetSum ]; unfold M at hu; change (∑ u:Glyph B h,X u • biasW G (i.val,j.val) ( Letters B u ))=0 at hu; simp_rw [ bias_C, smul_ite,smul_zero,sumKn ] at hu; exact hu
   exact Fintype.linearIndependent_iff.mp T.linearIndependent (fun k=> X ⟨i,j,k⟩ ) he k
private lemma starW (p: WickPol G)(c:ℂ): Free.realForm ( c • p )= star c • Free.realForm p:= by
    apply equalPol; intro q; rw [ Free.real_eval,map_smul,map_smul,Free.real_eval,smul_eq_mul,smul_eq_mul,star_mul' ]
lemma illumined (h:ℕ): LinearIndependent ℂ ( Letters B ( d:=h )):= by
    let V:= Letters B ( d:=h ); have he (X:Glyph B h→ℂ) (hx:∑ i,X i • V i=0):∀ i,( X i ).re=0:= by
       obtain hp:∑ i,( X i+ star ( X i ) ) • V i=0:= by simp_rw [ add_smul, Finset.sum_add_distrib, hx,zero_add ]; rw [← map_zero Free.realForm]; apply Eq.trans _ (congr_arg Free.realForm hx); rw [map_sum]; exact Finset.sum_congr rfl (fun k _=> by rw [starW,real_shell])
       have ht(t:ℂ): t+star t=(↑(2*t.re):ℂ):= Complex.add_conj _; simp_rw [ht, cling] at hp; intro i; exact (mul_eq_zero.mp ( (Fintype.linearIndependent_iff.mp ( indR B h )) _ hp i)).resolve_left (by norm_num)
    apply Fintype.linearIndependent_iff.mpr; intro g hg i; obtain hp:= he g hg i; obtain hx : ∑ i:Glyph B h,( I • g i ) • V i= 0:= by simp_rw [smul_eq_mul, mul_smul, ← Finset.smul_sum, show ∑ i:Glyph B h,g i • V i=0 from hg, smul_zero ]
    obtain hu := he _ hx i; change (I*(g i)).re=0 at hu; apply Complex.ext; exact hp; simpa using hu
abbrev Rune (B: Deck G)(i:Glyph B h): shellSector G h:=⟨ Letters B i, indoor B i⟩
def Daylight (h:ℕ): Module.Basis ( Glyph B h ) ℂ ( shellSector G h ):= Module.Basis.mk
   (v:=Rune B) ( by refine Fintype.linearIndependent_iff.mpr ?_; intro x hx i; apply Fintype.linearIndependent_iff.mp ( illumined B h ) x _ i; rw [show (∑ i:Glyph B h,x i • Letters B i)=( (shellSector G h).subtype ) (∑ i:Glyph B h,x i • Rune B i) from ?_,hx,map_zero ]; rw [map_sum]; rfl ) ( by
       let V:= Submodule.span ℂ (Set.range ( Rune B ( h:=h ) )); intro x _; suffices H:x.val∈ (Submodule.map ((shellSector G h).subtype) V) by obtain ⟨v,hv,hq⟩:= H; exact ( Subtype.ext hq : v=x ) ▸ hv
       unfold V; rw [Submodule.map_span, ← Set.range_comp ]; -- careful rw at x? host
       change _∈ policy B h; rw [cover_all B]; exact x.property )
end YM.MS.Theater
