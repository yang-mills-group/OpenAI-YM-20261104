import YM.RegulatorIR.Halo.Reels
import YM.RegulatorIR.Ward.Eddy

/-!
# Copy operation on quotient tori when ϑ shared
Scales expand number of original cells while actual root geometry unchanged.
Periodic eval of all quotient backgrounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge}{I J X:Type}{f c n m:Side}
variable (f m:Side)
section Counts
-- counting torus copies by summing functions. Easier use finite group hom and product with base cast fiber of equal divisibility
lemma cast_onto : Surjective (castSite m f):=by intro y; exact ⟨wrap _ (Lattice.lift y), (falls ..).trans (wrap_lift _)⟩

def counts (m:Side):ℝ:= (m.val:ℝ)^4
lemma tiles (F:Site f→ℝ): (∑ i:Site (m*f),F (castSite m f i))= counts m*∑ i:Site f,F i:=by
 -- finite group average. commute averaging over all translations of target
 let p:=castSite m f; let T:ℝ:=∑ i:Site f,F i; let t:ℝ:=∑ i:Site (m*f),F (p i)
 have he (v:Site f): (∑ i:Site (m*f),F (p i+v))=t:=by
    obtain ⟨y,rfl⟩:= cast_onto f m v
    simp_rw [show ∀ i,p i+castSite m f y=p (i+y) from fun i=>(map_add p i y).symm]; exact Equiv.sum_comp (Equiv.addRight y) (fun i=>F (p i))
 have ht(i:Site (m*f)):(∑ v:Site f,F (p i+v))=T:=Equiv.sum_comp (Equiv.addLeft (p i)) F
 have hh : (f.val:ℝ)^4*t=((m*f).val:ℝ)^4*T:=by
    have hp:(∑ v:Site f,∑ i:Site (m*f),F (p i+v))= ∑ i:Site (m*f),∑ v:Site f,F (p i+v):= Finset.sum_comm
    simpa only [he,ht,Finset.sum_const,Finset.card_univ,nsmul_eq_mul, site_card,Nat.cast_pow] using hp
 rw [PNat.mul_coe,Nat.cast_mul,mul_pow,mul_comm ((m.val:ℝ)^4),mul_assoc] at hh; exact mul_left_cancel₀ (pow_ne_zero _ (by exact_mod_cast f.property.ne')) hh

def shadow (x:OEdge (m*f)): OEdge f := index (castEdge m f x.val)
lemma coins (H:Even f.val)(U:OEdge f→ℝ): (∑ x: OEdge (m*f),U (shadow f m x))= counts m*∑ x: OEdge f,U x:=by
 let p (u:Edge (Site (m*f))) := U (index (castEdge m f u)); let q (u:Edge (Site f)):= U (index u)
 have hh : (∑ i :Edge (Site f),q i)= 2* ∑ x:OEdge f,U x:=by rw [Quadratic.doubles H ?_]; congr 1; apply Finset.sum_congr rfl; intro i _;unfold q; apply congr_arg; exact Subtype.ext i.property;intro i;exact congr_arg U (Subtype.ext (eR_reflect _))
 have hp : (∑ i,p i)=counts m *∑ i,q i:=by rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; change (∑ i:Site (m*f),∑ j:Axis, q ((castSite m f i),j))=_; exact tiles f m (fun i=>∑ j:Axis,q (i,j))
 rw [hh, Quadratic.doubles (f:=m*f) (Even.mul_left H m.val) (T:=p) ?_] at hp; change 2*(∑ i:OEdge (m*f),U (shadow f m i))= _ at hp; swap
 · intro i;unfold p; rw [reflectsE]; apply congr_arg;exact Subtype.ext (eR_reflect _)
 linarith
lemma echoes (H:Even f.val)(X:Type) [Fintype X](U:OEdge f × X →ℝ): (∑ x: OEdge (m*f) × X,U (shadow f m x.1,x.2))= counts m*∑ x:OEdge f × X,U x:=by rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; exact coins f m H (fun i=>∑ j,U (i,j))
end Counts

def stamped (x: Horizon G f): Horizon G (m*f):=fun i=> fire x (castEdge m f i.val)
variable {f}
lemma fire_t (x: Horizon G f)(h:Even f.val)(u): fire (stamped f m x) u=fire x (castEdge m f u):=by
 let t:=stamped f m x; let i:= Orb.index u; rcases eR_spec u with he|he
 · have hp: i.val=u:=he;change fire t u=_;rw [←hp, fire_at]; rfl
 have hp:i.val=reflect u:=he
 change fire t u=_; rw [show fire t u= -fire t i.val by rw [hp, fire_swaps t (h.mul_left m.val), neg_neg],fire_at];change -fire x (castEdge m f i.val) = _
 rw [hp,reflectsE,fire_swaps x h,neg_neg]
lemma fire_orb (x:Horizon G f)(h: Even f.val)(u) : orbLift (climb (stamped f m x)) u= orbLift (climb x) (castEdge m f u):=by
 rw [mat_expanded,mat_expanded,Work.F03.represent_link,Work.F03.represent_link]; simp only [canvas, show ∀ i:Axis, Exterior.axisEquiv.symm (Exterior.coord i)=i from fun i=>Exterior.axisEquiv.symm_apply_apply i,Prod.mk.eta];exact congr_arg G.lieExp (fire_t m x h u)

def signed (x: ℝ→Horizon G f)(t:ℝ):= stamped f m (x t)
def stampL : Horizon G f→ₗ[ℝ] Horizon G (m*f) where
 toFun:=stamped f m
 map_add' x y:=by ext1 i; unfold stamped fire;split_ifs <;> simp [*,add_comm]
 map_smul' r x:=by ext1 i; unfold stamped fire;split_ifs <;> simp [*]
lemma wave {x:ℝ→ Horizon G f} (h:ContDiffAt ℝ ∞ x 0) : ContDiffAt ℝ ∞ (signed m x) 0:= ((stampL m (f:=f) (G:=G)).toContinuousLinearMap.contDiff.contDiffAt).comp _ h
lemma waveV {x y:ℝ→ Horizon G f} (h:Even f.val)(he:Ward.reel_prop x y): Ward.reel_prop (signed m x) (signed m y):=by
 filter_upwards [he] with t ht;obtain ⟨k,hk,H⟩:=ht
 let z:=k ∘ castSite m f
 have hz:compatible z:=fun i=> (congr_arg k (map_neg ..)).trans (hk _)
 refine ⟨z,hz,?_⟩
 ext1 i; let U:= climb (t • y t)
 have hm(w:ℝ→ Horizon G f) (i: Edge (Site (m*f))): orbLift (climb (t • signed m w t)) i= orbLift (climb (t • w t)) (castEdge m f i):=by rw [show t • signed _ _ _= _ from ((stampL m).map_smul t (w t)).symm]; exact fire_orb m _ h _
 let a:=castEdge m f i.val
 rw [← lift_at (climb (t • signed m x t)),← lift_at (goat _ _)]; change orbLift (climb _) _= orbLift _ _; rw [hm,H,goat_lift _ _ hk,goat_lift z _ hz]; unfold Lattice.gauge;rw [show _ = _ from hm y i.val]
 unfold z castEdge; simp only [Function.comp_apply]; rw [map_add,val_step]

variable {l P:ℝ} (h:Even f.val)(hp:l*f.val=P)
def playS (h:Even f.val)(hp:l*f.val=P): Deck ((m.val:ℝ)*P) (Foot G) (Book G (m*f)):= Carto G l _ (h.mul_left _) (by rw [← hp,PNat.mul_coe,Nat.cast_mul];ring)
lemma time_v (x:Horizon G f): bridge (playS m h hp) (paper G (m*f) (stamped f m x))=bridge (Carto G l P h hp) (paper G f x):=by
 ext1 p
 rcases p with ⟨t,i⟩; unfold playS;rw [firebrand,firebrand]
 rw [fire_t m x h, fallen]
lemma steering (d: Motion) i : (playS m (G:=G) h hp).wind d i=(Carto G _ _ h hp).wind (filling m d) i:= Prod.ext (filling_v ..).symm rfl
-- kernel sti and ancestry. No terminal outside W.Prev.
lemma stiff (x: Horizon G f) {N:Layer (Foot G) (Foot G)}(H:Layer.Sym (Carto G l P h hp) (Carto G l P h hp) N)(B:Billed N): let A:=Carto G l P h hp; let Q:=playS m (G:=G) h hp; beneath (fmat Q Q N) (stamped f m x)= counts m * beneath (fmat A A N) x:=by
 intro A Q;let p:= stamped f m x
 let K:= fmat Q Q N; let L:=fmat A A N
 let u:= (paper G f).symm (L*ᵥ paper G f x);let u':= (paper G (m*f)).symm (K*ᵥ paper G (m*f) p)
 have hx : u'= stamped f m u:=by
    apply (paper G _).injective;ext1 i;rw [show paper G _ u'= _ from (paper G _).apply_symm_apply _];let z:= Q.place i
    have hs(v:Book G (m*f)→ℝ): v i= bridge Q v z:=by unfold bridge z;rw [Deck.north,Q.placed,one_mul]
    have hz: Layer.Sym Q Q N := by
       intro d u v; rw [show Q.wind d u=_ from steering m h hp d u,show Q.wind d v=_ from steering m h hp d v];exact H ..
    rw [hs (K *ᵥ _),hs (paper G _ _),show bridge Q _=bridge A (paper G f u) from time_v m h hp u]; unfold K u L;rw [LinearEquiv.apply_symm_apply,← StopB.row_times N B (A:=A) H,← StopB.row_times N B hz]
    unfold Q p A; simp_rw [time_v m h hp x]
 rw [beneath, beneath, Quadratic.phase,Quadratic.phase,← show (paper G (m*f)) u'= _ from (paper G _).apply_symm_apply _,hx]; unfold dotProduct
 rw [← show paper G f u= _ from (paper G f).apply_symm_apply _]
 have hh(i:OEdge (m*f)) (j:G.ColorIndex): paper G _ (stamped _ _ x) (i,j)*paper G _ (stamped _ _ u) (i,j)=paper G _ x (shadow f m i,j)*paper G _ u (shadow f m i,j):=by change fire x _ _ * fire u _ _= _; unfold fire; split_ifs <;> first|rfl|(rw [PiLp.neg_apply, PiLp.neg_apply,neg_mul_neg];rfl)
 rw [Finset.sum_congr rfl (g:=fun i:Book G (m*f)=> paper G f x (shadow f m i.1,i.2)*paper G f u (shadow f m i.1,i.2)) (fun i _=> hh i.1 i.2)]; rw [show (∑ i:Book G (m*f), paper G f x (shadow f m i.1,i.2)* _) = _ from echoes f m h G.ColorIndex (fun i=>paper G f x i*paper G f u i)]; ring
end YM.RegulatorIR.Halo
