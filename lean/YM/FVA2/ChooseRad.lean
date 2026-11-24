import YM.FVA2.RadBook
/-!
# Prove uniqueness of the open-only Jrad optic: the specified off-shell lifts at h (closest
 linear projection in Taylor jet gauge) determine all evanescent values as well. This
 differs from asserting that any basis-independent or contact-producing generators involving
 D-specific contractions have no evanescents; as in `Mach.Gallery`, only open-axis values with
 indices from the four arms. Pairing singular pole traces is later. 
 -/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 510000
namespace YM.MS.RadL
open Set Function Filter Finset MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Book.Convolve
open Theater Mach Lifting Pole Color Arts Pilot Spin Motif Literal Halo Rock Path Oceans Pearl
open scoped Topology Classical ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{d t h k n m:ℕ}
namespace Spray
variable (ν:Axis) (z:ℂ) (ℓ γ:Axis)(p:E4)(L:Legs (Shore G n))
private lemma anti (z:ℂ) (u:List Axis) (i j:Axis): Pole G n i j z u= -Pole G n j i z u:= by
    induction u with
    | nil=>
       simp only [ Pole,cur ]; rw [show F₀ (G:=G) ( chair n i ) ( chair n j )= - F₀ (chair n j) ( chair n i ) from (neg_sub ..).symm, jaw_skew ( realA _ ).tune ( realA _ ).tune, cross_false',neg_one_smul , smul_neg, neg_add ] --
    | cons a u ih=> rw [Pole,Pole, ih,map_neg]
-- finite expansion in real homogeneous polynomials, vector dimension encoded in Lett.
abbrev LensL (G:Gauge)(n:ℕ):= Rack G n
/-- Tube k colors assembled from complex row in W. Gives Taylor G k, evaluated at x.
 simultaneous conjug (vis x logs). Works at z formal complex values. -/
abbrev spiral (G:Gauge)(n:ℕ)(k:ℕ)(z:ℂ) (p:Axis)(s:E4)(c:G.ColorIndex):= pole ⟨ k,p,s ⟩ z c n -- arg order pole n explicit
lemma planeCalls (s:E4)(l:Legs (Shore G n)) (k:ℕ): ∑ i:Axis, (s i:ℂ) • ( fun c:G.ColorIndex=>spiral G n k z i s c l )=0:= by
    -- forall c. pair sum cancel.Observe Finset. include k basis.
    funext c; simp_rw [ Finset.sum_apply, Pi.smul_apply, spiral, pole ]; -- unfold Finset nested?
    let f (i j:Axis)(v:Fin k→Axis):ℂ:= ( s i :ℂ)* (s j:ℂ)*( ( ( (k:ℝ)+2)⁻¹ * Theater.amount k * ∏ i:Fin k,s ( v i ) :ℝ ):ℂ )* Pole G n j i z (List.ofFn v) c l;
    have hx(i j:Axis)(v: Fin k→Axis): f i j v= -f j i v:= by unfold f; rw [ anti z _ j i ]; simp only [ Pi.neg_apply ]; ring
    have he : ∑ i:Axis,∑ j:Axis,∑ v:Fin k→Axis,f i j v=0:= by
        let χ:=∑ i:Axis,∑ j:Axis,∑ v: Fin k→Axis,f i j v; have h0:χ=-χ:= by
            unfold χ; rw (occs:=.pos [1]) [Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib ]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; exact Finset.sum_congr rfl fun v _=> hx j i v
        exact neg_eq_self.mp h0.symm
    rw [ Pi.zero_apply, ← he ]; simp_rw [ Finset.sum_apply,Fintype.sum_prod_type, Finset.smul_sum ]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _=> ?_; simp only [Pi.smul_apply,smul_eq_mul ]; unfold Pole_leaf plaq factor f; simp only; push_cast; ring
private def grain (U:G.Color) : ∀ {k:ℕ}, (Fin k→ Axis) → Tensor.T E4 G.Color k
    | 0,_=> ContinuousMultilinearMap.constOfIsEmpty ℝ ( fun _: Fin 0=>E4 ) U
    | _+1,A=> Tensor.added (grain U (A ∘ Fin.succ)) ( compAxis (A 0) )
lemma grain_d (U:G.Color)(k:ℕ)(A:Fin k→Axis): diagonal (grain U A) p= (∏ i:Fin k,p ( A i )) • U:= by induction k with| zero=> rw [Fin.prod_univ_zero,one_smul]; rfl| succ k ih=> rw [grain,Tensor.added_diag, ih,smul_smul, Fin.prod_univ_succ]; rfl
lemma grain_s (U:G.Color)(k:ℕ)(A:Fin k→Axis) : Tensor.Sym (grain U A):= by cases k with| zero=> exact fun _ _=> rfl| succ k=> exact added_sym (grain U ( A ∘ Fin.succ )) ( compAxis ( A 0 ) )
def tubeL (Q:ℂ→ₗ[ℝ] ℝ)(k:ℕ)(i:Axis)(A: (Spray.mk k i 0).Λ): G.Color := WithLp.toLp _ fun c:G.ColorIndex=> (((k:ℝ)+2)⁻¹* Theater.amount k)*Q (Pole G n A.1 i z (List.ofFn A.2) c L)
def Day (Q:ℂ→ₗ[ℝ] ℝ)(k:ℕ) (i:Axis): Tensor.T E4 G.Color (k+1):= ∑ A:(Spray.mk k i 0).Λ, grain ( tubeL z L Q k i A ) ( Fin.cons A.1 A.2 )
lemma Day_value (Q:ℂ→ₗ[ℝ] ℝ)(k:ℕ) (i:Axis)(c:G.ColorIndex)(p:E4): diagonal (Day z L Q k i) p c= Q (spiral G n k z i p c L):= by
    unfold spiral Day pole; simp_rw [ Finset.sum_apply,map_sum ]; -- diagonal
    have hr {I:Type}(A:Finset I)(X:I→Tensor.T E4 G.Color (k+1)) : diagonal (∑ i∈A,X i) p c=∑ i∈A,diagonal (X i) p c:= by unfold Tensor.diagonal; rw [_root_.sum_apply ]; exact map_sum (EuclideanSpace.proj (𝕜:=ℝ) (ι:=G.ColorIndex) c) _ _
    rw [hr ]; refine Finset.sum_congr rfl fun ⟨x,y⟩ _=>?_ ; rw [grain_d ]; simp only [ PiLp.smul_apply,Fin.prod_univ_succ, Pi.smul_apply,Fin.cons_zero,Fin.cons_succ ]; let t: Spray:= ⟨k,i,p⟩; change _= Q ( ( t.factor ( x,y ) :ℝ) • _ ); rw [map_smul ]; change ( p x*(∏ i: Fin k,p ( y i ) ) )*(_*_*Q _)= (_*_*_*(∏ i: Fin k,p ( y i ) ))* Q _; unfold t Pole_leaf plaq; simp only; ring
/-- open-leg Taylor valued in Color coordinates (e.g. split into real and imaginary).
 Note: uses external open dimension, no assertion for comparison with other evanescent choices.
-/
def sky (Q:ℂ→ₗ[ℝ] ℝ)(k:ℕ) : Labels.Taylor G k := ⟨ Day z L Q k, fun i a v=> by unfold Day; rw [_root_.sum_apply,_root_.sum_apply ]; exact Finset.sum_congr rfl (fun j _=> ( grain_s (tubeL ..) (k+1) ( Fin.cons _ _ ) ) a v), fun s=> by
       ext1 c; let f:= EuclideanSpace.proj (𝕜:=ℝ) (ι:=G.ColorIndex) c; change f ( ∑ i:Axis,s i • Tensor.diagonal (Day z L Q k i) s ) = _; rw [map_sum ]; simp_rw [map_smul];
       simp_rw [ show ∀ i: Axis,f (diagonal (Day z L Q k i) s)= Q _ from fun i=> Day_value z L Q k i c s ]; rw [ show WithLp.ofLp (p:=2) (0:G.Color) c= 0 from rfl,← map_zero Q ]; simp_rw [ ← map_smul,← map_sum ]; congr 1;  simp_rw [Complex.real_smul ]; obtain hh:= congr_fun (planeCalls z s L k) c; rw [Finset.sum_apply ] at hh; exact hh -- ℝ vs ℂ smul. adjust
   ⟩
lemma own (f:Spray)(Q:ℂ→ₗ[ℝ]ℝ)(c:G.ColorIndex) : f.α c ( sky z L Q f.k)= Q ( f.pole z c n L ):= Day_value ..
lemma pure_t (f:Spray)(c:G.ColorIndex) : f.pole z c n∈ Theater.Dark (Plane.field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex)) (P:=Arts.SectorP n)):= by
   unfold pole; apply (Dark ( Plane.field ( P:=Arts.SectorP n ) ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex) ) )).sum_mem; intro i hi; refine smul_mem _ _ ?_; exact (Pole.ingot ( f.plaq i ).i ( f.plaq i ).j ( f.plaq i ).jets).2.tune c
-- preserve Pure throughout view.Kappa.C. act light shape.
end Spray
section close
open Spray
variable (L:Legs (Shore G n))(k:ℕ)(z:ℂ)
local notation "Φ(" G "," n ")" => (Plane.field ( P:= Arts.SectorP n ) ( Landau.parity ( A:=Arts.L n ) ( C:=Gauge.ColorIndex G ) ))
private def nail (G: Gauge)(k:ℕ)(z:ℂ)(n:ℕ): Module.Dual ℝ (Labels.Taylor G k) →ₗ[ℝ] Rack G n where
   toFun q l:= ( q (sky z l Complex.reCLM.toLinearMap k):ℂ) + Complex.I * ( q ( sky z l Complex.imCLM.toLinearMap k ):ℂ );
   map_add' f g:= by funext l; simp only [LinearMap.add_apply,Pi.add_apply,Complex.ofReal_add,mul_add ]; ring
   map_smul' x f:= by funext l; simp only [LinearMap.smul_apply,RingHom.id_apply, Pi.smul_apply,Complex.real_smul,smul_eq_mul,Complex.ofReal_mul ]; ring
private lemma spark (f:Spray)(c:G.ColorIndex) : nail G f.k z n ( f.α c )= f.pole z c n:= by
    funext l; unfold nail; dsimp only [LinearMap.coe_mk,AddHom.coe_mk ]; rw [ own, own,mul_comm Complex.I ]; exact Complex.re_add_im _
private def Vℓ (G:Gauge)(n:ℕ)(z:ℂ)(k:ℕ): (Module.Dual ℝ (Labels.Taylor G k))→ₗ[ℝ] ↥(Theater.Dark Φ(G,n)) := (nail G k z n).codRestrict (( Theater.Dark Φ(G,n) ).restrictScalars ℝ) fun f=> by
   have hq : familyR G k ≤ Submodule.comap (nail G k z n) (( Theater.Dark Φ(G,n) ).restrictScalars ℝ):= by
      apply Submodule.span_le.mpr; rintro f ⟨ y,i,c,rfl⟩; let t:Spray:= ⟨k,i,y⟩; change nail G t.k z n (t.α c)∈ Theater.Dark Φ(G,n); rw [spark z t c ]; exact Spray.pure_t z t c
   exact hq ( show f∈ familyR G k from ( by rw [fullR]; exact mem_top ) )
-- build dim orbit. Then show p=M lift directly.Nested.Scalar.κ.
abbrev regX (G:Gauge)(z:ℂ)(n:ℕ) : Pol G→ₐ[ℂ] ↥(Theater.Dark Φ(G,n)):= MvPolynomial.aeval fun (i:Key G)=> Vℓ G n z i.1 ( ( Labels.axes G i.1 ).coord i.2 )
private lemma fullα (i:Spray)(j:G.ColorIndex): i.α j=∑ u,( i.α j (Labels.axes G i.k u)) • (Labels.axes G i.k|>.coord u ) := by
    let f:= i.α j; ext t; nth_rw 1 [← (Labels.axes G i.k).sum_repr t]; simp only [LinearMap.sum_apply,map_sum,map_smul, LinearMap.smul_apply ]; exact Finset.sum_congr rfl fun j _=> mul_comm (G:=ℝ) _ _
lemma at_page (i:Spray)(j:G.ColorIndex) (n:ℕ): (regX G z n (page i.k ( i.spot j ) ) ).val= i.pole z j n:= by
    let F:= (Theater.Dark Φ(G,n)); let V:= Vℓ G n z i.k; rw [show i.pole _ _ _=( V ( i.α j ) ).val from (spark z i j).symm]; congr 1; -- support? reduces via equality?
    unfold page; rw [map_sum, fullα i j, map_sum ]; simp_rw [map_smul, LabelC,regX, MvPolynomial.aeval_X ]; rfl -- cast.R.M
abbrev active (G:Gauge)(k:ℕ)(z:ℂ) : Pol G→ₗ[ℂ] Rack G k:= (Theater.Dark Φ(G,k)).subtype ∘ₗ ( regX G z k ).toLinearMap
lemma timesA (p q:Pol G)(n:ℕ): active G n z (p*q)=Motif.bite n G (active G n z p) (active G n z q):= by change ( regX G z n (p*q) ).val=_; rw [ map_mul ]; rfl
-- criterion when extending source Requests. Uses ALL dimension parameters before traces. No asumptions.
variable (T: Fin m→ Spray)(σ:Lifting.Grid G m)
abbrev notationPad := ∏ i:Fin m,page (T i).k ((T i).spot (σ i))
lemma facts_t : notationPad T σ= ∏ i:Fin m,page (T i).k ((T i).spot (σ i)):= rfl
private lemma wageN0 (T:Fin (m+1)→ Spray): bill T= (T 0).k+2+ bill (T ∘ Fin.succ):= by unfold bill; rw [Fin.sum_univ_succ]; rfl
lemma pure_t : At (notationPad T σ) (bill T,m):= by
    induction m with
    | zero=> simp_rw [facts_t, Fin.prod_univ_zero ]; rw [ show bill T=0 from Fin.sum_univ_zero _ ]; exact MvPolynomial.isWeightedHomogeneous_one ℂ bidegree
    | succ m ih=>
        rw [ facts_t, Fin.prod_univ_succ, wageN0 ];
        let P:= page (T 0).k ((T 0).spot ( σ 0 )); let Q:= notationPad (T ∘ Fin.succ) (σ ∘ Fin.succ); have h1 : MvPolynomial.IsWeightedHomogeneous bidegree P (( T 0 ).k+2,1):= bypage _; obtain ht : MvPolynomial.IsWeightedHomogeneous bidegree Q (bill ( T ∘ Fin.succ ),m):= ih _ _;
        rw [show ( (T 0).k+2+bill (T ∘ Fin.succ),m+1 )=( (T 0).k+2,1 )+ (bill (T ∘ Fin.succ), m) from Prod.ext rfl (by change m+1=1+m; omega ) ]; exact h1.mul ht
lemma lights_t : active G n z (notationPad T σ)= prodS ℂ ( bite n G ) ( coin 1 ) m (fun i=> Spray.pole (T i) z (σ i) n ):= by induction m with | zero=> unfold notationPad; rw [Fin.prod_univ_zero ]; exact Eq.trans (congr_arg Subtype.val (map_one ( regX G z n ))) rfl | succ i ih=> rw [facts_t, Fin.prod_univ_succ, timesA,show active G n z (page _ _)=_ from at_page z (T 0) (σ 0) n ]; exact congr_arg _ ( ih (T ∘ Fin.succ) (σ ∘ Fin.succ) )
lemma Free_t : Theater.orbit G ( notationPad T σ )= prodS ℂ ( bite 0 G ) ( coin 1 ) m (fun i=> Spray.pole (T i) 0 (σ i) 0 ):= by
    induction m with | zero=> unfold notationPad; rw [ Fin.prod_univ_zero ]; exact ( show (opA G 1).val=_ from Eq.trans (congr_arg Subtype.val ( map_one (opA G) )) rfl )| succ i ih=> rw [facts_t, Fin.prod_univ_succ, bags, pageX, ← Spray.trust , ← Spray.pole_value ]; exact congr_arg _ ( ih _ _ ) -- defeq?
-- Thus base mark p chosen across ext. star.linear sum.
abbrev Corona (G:Gauge) (T:Fin m→ Spray)(σ:Lifting.Grid G m) : Pol G:= ∑ i:Lifting.Grid G m,( Lifting.group G i σ:ℂ) • notationPad T i
lemma qualifies : At ( Corona G T σ ) (bill T,m):= sum_mem (fun i _=> Submodule.smul_mem _ _ (RadL.pure_t T i)) -- implicit ring
lemma reality (n:ℕ)(z:ℂ): active G n z ( Corona G T σ )= Word G T σ z n:= by
   unfold Corona; rw [map_sum, reads ]; simp_rw [map_smul,lights_t ]
lemma heritage : Theater.orbit G (Corona G T σ)= Word G T σ 0 0:= by unfold Corona; rw [map_sum,reads ]; simp_rw [map_smul,Free_t ]
-- span.V.Sample
structure Recipe (X: Coat G)(p:Pol G) (h m:ℕ): Prop where
   grade : At p (h,m)
   lift : X 0 0= Theater.orbit G p
   vision (z:ℂ) (n:ℕ) : X z n= active G n z p
lemma accepts (X:Coat G)(h:X∈ Dome G d m):∃ p,Recipe X p d m:= by
   refine Submodule.span_induction (p:=fun W _=>∃ p,Recipe W p d m) ?_ ?_ ?_ ?_ h
   · rintro x ⟨ T,σ,h,rfl⟩; rw [ ← h ]; exact ⟨ _, qualifies T σ, ( heritage T σ ).symm,fun z n=> (reality T σ n z).symm⟩
   · exact ⟨0, zero_mem _,( map_zero _ ).symm, fun z n=>(map_zero _).symm⟩
   · rintro X Y hx hy ⟨p,hp⟩ ⟨t,ht⟩; exact ⟨ p+t, Submodule.add_mem _ hp.grade ht.grade,(by rw [Pi.add_apply,Pi.add_apply,map_add,hp.lift,ht.lift ]), fun z n=> by rw [Pi.add_apply,Pi.add_apply,map_add,hp.vision,ht.vision ] ⟩
   rintro x A h ⟨p,hp⟩; refine ⟨ (x:ℂ) • p, Submodule.smul_mem _ _ hp.grade,(by rw [Pi.smul_apply,Pi.smul_apply,map_smul,hp.lift ]; rfl), fun z n=> by rw [Pi.smul_apply,Pi.smul_apply,hp.vision,map_smul ]; rfl ⟩ -- rfl underlying
lemma sharp (X: Coat G)(he:X∈ Dome G h m) {p: Pol G}(hP:At p (h,m))(ht:X 0 0= Theater.orbit G p): Recipe X p h m:= by
    obtain ⟨u,hu⟩:= accepts _ he; rw [← opaqueL hu.grade hP ( hu.lift.symm.trans ht ) ]; exact hu
-- Therefore radial angular continuation prescription matches X and bare. No datum required after Reg choices.V.Do general d.
open FVA2 FVA2.ColorCode
lemma exact_optics {B:Local.Physical.Deck G}{W:Land.Booked B}(i: Land.Plaid B d)(h:Reg W): Recipe (fun z=> value _ z ( W.optics d i )) (Warehouse.label B d (Land.read i).grade i.2).val d (Land.read i).grade:= by
    obtain hr:= h d i; apply sharp _ hr; exact ((filmW B i.2).2); rw [low_row ]; exact (W.law d i).2.trans (Warehouse.scheme B i.2)
-- unique Reg. salvage rotational 
lemma unique {B:Local.Physical.Deck G}(A P: Land.Booked B)(h:Reg A)(he:Reg P): A=P:= by
   have hL (d:ℕ)(i:Land.Plaid B d) : A.optics d i= P.optics d i:= by
       let U:= A.optics d i; let V:= P.optics d i; have huv(z:ℂ): value (Mob G) z U=value _ z V:= funext fun n=> ( exact_optics i h|>.vision z n ).trans ( exact_optics i he|>.vision z n ).symm
       ext k n l; apply sub_eq_zero.mp; exact Motif.valuedZ ( U-V ) ( Garment.Wave.slice l ) ( fun z=> by rw [ map_sub, huv,sub_self,map_zero ] ) k
   cases A; cases P; congr; exact funext fun i=>funext (hL i)
end close
end YM.MS.RadL
