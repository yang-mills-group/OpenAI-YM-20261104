import YM.RegulatorIR.Warm.Pencil

/-!
# Charge β transport through leading graph exactly. Independent of any
longitudinal decay. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Warm
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {G:Gauge}{X X' Y W Z L:Type}{b c e p:ℕ}
-- elementary layer frame and billed. generic thermostat
lemma ledgerU {K:Layer X X'} -- X'
    {V:Layer X Y}(h:Billed K)(ht:Billed V):Billed (fun x p=>Sum.elim (K x) (V x) p):=by
 obtain ⟨v,h,H⟩:=h;obtain ⟨u,h',Hp⟩:=ht; refine ⟨v+u,by finiteness,fun x=>?_⟩
 rw [quota_base]; rw [Summable.tsum_sum ENNReal.summable ENNReal.summable] -- inspect
 apply add_le_add _ _ <;> rw [← quota_base]; exact H _; exact Hp _
lemma ledgerB {K:Layer X W}{V:Layer Y W}(h:Billed K)(ht:Billed V): Billed (Sum.elim K V):=by obtain ⟨v,h,H⟩:=h;obtain ⟨u,h',Hp⟩:=ht; exact ⟨v+u,by finiteness,fun x=>Sum.casesOn x (fun i=>(H i).trans le_self_add) (fun i=> (Hp i).trans le_add_self)⟩
lemma shanks {Q:Layer Y X} (h:Billed Q)(hp:Billed (Function.swap Q)): Billed (shank Q)∧ Billed (Function.swap (shank Q)):=by
 refine ⟨ledgerU (K:=-Q) (V:=ID Y) h.neg billed_id,?_⟩
 rw [show Function.swap (shank Q)= Sum.elim (Function.swap (-Q)) (Function.swap (ID Y)) from funext (fun i=>by cases i <;> rfl),show Function.swap (ID Y)=ID Y from funext (fun i=>funext (fun j=>by simp [ID,Function.swap,eq_comm]))]; exact ledgerB hp.neg billed_id

def warmP (c:ℝ)(Q:Layer Y X) := c • lap (Function.swap (shank Q)) (shank Q)
-- pull.Jm.D phase and writing in J precision public.
def entryK (K:Layer X X) : Layer (X ⊕ Y) (X⊕Y):= Quadratic.glued K 0 0 0
def flareK (c:ℝ)(Q:Layer Y X)(K:Layer X X) : Layer (X⊕Y) (X⊕Y):=entryK K + warmP c Q
def stemY (p:Layer X Y):Layer (X⊕Y) Y:= Sum.elim p (ID Y)

lemma entry_fee {K:Layer X X}(h:Billed K):Billed (entryK K (Y:=Y)):=by
 have hz{W Z:Type}: Billed (0:Layer W Z):=by
    refine ⟨0,by finiteness,fun x=>?_⟩; exact (quota_zero _).le
 rw [show entryK K (Y:=Y)= Sum.elim (fun x t=> Sum.elim (K x) 0 t) 0 from ?_]
 exact ledgerB (ledgerU (V:=0) h hz) hz
 ext1 i; ext1 j; cases i <;> cases j <;> rfl
lemma chargedV {D:Layer X Y} (h:Billed D)(ht:Billed (Function.swap D)):Billed (stemY D) ∧ Billed (Function.swap (stemY D)):=by
 refine ⟨ledgerB h billed_id,?_⟩
 rw [show Function.swap (stemY D)=(fun x p=> Sum.elim (Function.swap D x) ((ID Y) x) p) from funext (fun x=> funext (fun z=>by cases z <;> first|rfl |simp [ID,Function.swap,stemY,eq_comm]))]; exact ledgerU ht billed_id
lemma flare_f {K:Layer X X}{Q:Layer Y X}(h:Billed K)(hv:Billed Q)(hk:Billed (Function.swap Q))(v:ℝ) : Billed (flareK v Q K) :=by obtain ⟨ha,hb⟩:=shanks hv hk; exact (entry_fee h).add ((hb.lap ha).smul v)

variable {P:ℝ}{A:Deck P X W}{B:Deck P Y L}{K N:Layer X X}{K':Layer Y Y}{D:Layer X Y}{Q:Layer Y X} {a:W→Prop}{v:ℝ}
variable (H: Quadratic.Bedload A B v a K K' Q D N) (hd:Billed (Function.swap D))
-- harvest lock: stationarity condition only on active fiber.
lemma laps_p {M:Layer X Y}{S:Layer X Y}{N:Layer Y Z} (h:Billed M)(ht:Billed S)(hv:Billed N): lap (M+S) N=lap M N+lap S N:= by ext1 i;ext1 j;unfold lap; simp only [Pi.add_apply,add_mul]; exact (Momentum.counts_profile h hv ..).tsum_add (Momentum.counts_profile ht hv ..)
lemma laps_n {M:Layer X Y}{N:Layer Y Z}(t:ℝ) : lap (t • M) N=t • lap M N:=by ext1 i;ext1 j;unfold lap; simp only [Pi.smul_apply, smul_eq_mul, mul_assoc,tsum_mul_left]
include H hd
local notation "Lt" => lap (flareK v Q K) (stemY D)
lemma stings : lap (Function.swap (stemY D)) (lap (flareK v Q K) (stemY D))=K':=by
 obtain ⟨h₁,h₂,h₃,h₄,h₅⟩:= H.rows; obtain ⟨he,hx⟩:= shanks h₂ h₃; obtain ⟨hP,hM⟩:= chargedV h₄ hd
 let F:= stemY D; let R:= shank Q
 let U:= ID Y-lap Q D
 have hZ : lap R F=U:=by
    ext1 x;ext1 y
    have ht:= counts_profile he hP x y; rw [lap,(ht.comp_injective Sum.inl_injective).tsum_sum (ht.comp_injective Sum.inr_injective)];
    change (∑' i:X,-Q x i*D i y)+(∑' i:Y, ID _ x i* ID _ i y)=ID _ x y-lap Q D x y
    simp_rw [neg_mul]; rw [tsum_neg,tsum_eq_single (b:=x),add_comm, ID, if_pos rfl,one_mul]; exact Eq.symm (sub_eq_add_neg ..)
    intro i hi; rw [show ID _ x i=0 from if_neg (show x≠i from Ne.symm hi),zero_mul]
 have hT : Lt=lap (entryK K) F + v • lap (Function.swap R) U:=by rw [flareK,warmP,laps_p (entry_fee h₁) ((hx.lap he).smul v) hP,laps_n,← lap_tools hx he hP,hZ]
 have hh : Billed U:= billed_id.sub (h₂.lap h₄)
 have hp(x:Y)(y): Lt (Sum.inr x) y=K' x y:=by
    have hf: lap (entryK K) F (.inr x) y=0:=by
              rw [lap]; change (∑'z,entryK K (Sum.inr x) z * _)= (0:ℝ); have he(z):entryK K (Sum.inr (x:Y)) z=0:= by cases z <;> rfl -- fix shadow
              simp_rw [he,zero_mul];exact tsum_zero
    change Lt (Sum.inr x) y=_
    rw [hT, Pi.add_apply,Pi.add_apply,hf,zero_add,← H.energy,Pi.smul_apply,Pi.smul_apply];unfold lap
    change v • (∑' i,R i (.inr x)*U i y)= v • U x y;apply congr_arg; rw [tsum_eq_single x]; simp [R,shank,ID]
    intro z ht;rw [show R z (.inr x)=0 from if_neg (show z≠x from ht),zero_mul]
 have hz(x:X) (hx:a (A.orbit x))(y:Y) : Lt (Sum.inl x) y=0:=by
    have hF:lap (entryK K) F (Sum.inl x) y=lap K D x y:=by
                   unfold lap;rw [← (Sum.inl_injective (α:=X) (β:=Y)).tsum_eq]; rfl
                   rintro (z|z) hz; exact ⟨z,rfl⟩;exfalso; apply hz;change (0:ℝ)*_=0;simp
    have hG:lap (Function.swap R) U (Sum.inl x) y= -(lap (Function.swap Q) U x y):=by
                   unfold lap; change (∑' i,(-Q i x)*U i y)= -(∑' i, Q i x* U i y); simp_rw [neg_mul,tsum_neg]
    have hxq:= congr_fun (congr_fun H.sheet x) y; unfold clipL at hxq; simp only [Function.comp_apply,if_pos hx] at hxq
    have hR: lap (Function.swap Q) (ID Y) x y=Q y x :=by
                   unfold lap; rw [tsum_eq_single y]; rw [ID, if_pos rfl, mul_one]
                   intro i hi; rw [ID,if_neg hi,mul_zero]
    unfold stableL at hxq;rw [laps_p h₁ ((h₃.lap h₂).smul _) h₄,laps_n,Pi.add_apply, Pi.add_apply,Pi.smul_apply] at hxq
    rw [hT,Pi.add_apply,Pi.add_apply,hF,Pi.smul_apply,Pi.smul_apply,hG,show U=ID Y-lap Q D from rfl,lapR h₃ (h₂.lap h₄) billed_id, Pi.sub_apply,Pi.sub_apply,hR,lap_tools h₃ h₂ h₄]
    change lap K D x y+v * lap (lap (Function.swap Q) Q) D x y=v*Q y x at hxq; rw [smul_eq_mul]; linarith
 ext1 x;ext1 y; have Hf : Billed Lt:= (flare_f h₁ h₂ h₃ v).lap hP
 unfold lap; rw [tsum_eq_single (b:=Sum.inr x)];
 · change ID Y x x * Lt (Sum.inr x) y=_;rw [ID,if_pos rfl,one_mul]; exact hp ..
 rintro (i|i) hi
 · change D i x * Lt (.inl i) y=_; by_cases he:a (A.orbit i) <;> first| rw [H.mean _ _ he,zero_mul]|rw [hz _ he,mul_zero]
 change ID _ i x * _ = _; rw [ID, if_neg (fun (h':i=x)=>hi (congr_arg _ h')),zero_mul]
end YM.RegulatorIR.Warm
