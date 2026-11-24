import YM.XSpace.Darling

/-!
# Wide region away from the perturbative normalization stations

Vector-family interface, Breathe requests. Keep coverage on all physical
separated sites, including exact marker-wall points as necessary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stall
open Function Filter Set MeasureTheory Lattice Mu Trace Furlough MvPolynomial Next.Rank.Normal Contraction JetGauge Future Drama Scale Shade Tide Further.FreeCovariance.KP Playpen
open Chart2 (V3 pit)
open Sail (cover reach)
open scoped Topology BigOperators ContDiff
variable {ι Y I:Type} {L:Filter ι} {G:Gauge}{a:ι→ℝ} {k:ℕ}
variable (c:Shade.Cut)(s:Finset I) (F:I→ι→Cover)

def spill (a:ℝ)(S:I→ Cover)(x:Cover):ℂ:= 1-∑ i∈s, pace c a (x-S i)
def porch (F:I→E4) (i:E4):Prop:=∀ j∈s,F j ≠ i
def Cleared (w:I→E4)(s:Finset I):Prop:=∀ i∈s,∀ j∈s,i≠j→ 5*c.rOut≤ ‖w i-w j‖
variable {s F} {w:I→E4}
variable {v:ℝ} in
lemma walled {F:I→Cover} (Z:∀ i∈s,∀ j∈s,i≠j →2*c.rOut≤ ‖actual v (F i-F j)‖)(hv:0<v){x:Cover} (h: spill c s v F x≠0) (i:I)(hi:i∈s): c.rIn ≤2*v*reach (x-F i):=by
  apply le_trans _ (Shade.size_actual hv (x-F i)).2
  by_contra! hp; classical
  apply h; rw [spill,Finset.sum_eq_single i,cut_inside c _ _ hv hp.le,sub_self]; swap; · simp [hi]
  intro j hj hk; by_contra he; obtain ⟨_,hh⟩:=tag c _ _ he; have ht:=Z j hj i hi hk; have he:actual v (F j - F i)=actual v (x-F i)-actual v (x-F j):=by unfold actual; rw [← smul_sub, ← Cross.rcast_sub, show x-F i-(x-F j)=F j-F i by abel]
  rw [he] at ht; linarith [norm_sub_le (actual v (x-F i)) (actual v (x-F j)), c.rIn_lt_rOut]
lemma fence {W:Type*}{x y:W→Cover}{a:W→ℝ}(L:Filter W)(u v:E4) (hx:Tendsto (fun i=> actual (a i) (x i)) L (𝓝 u))(hy:Tendsto (fun i=> actual (a i) (y i)) L (𝓝 v)):Tendsto (fun i=> actual (a i) (x i-y i)) L (𝓝 (u-v)):=by simp_rw [actual,Cross.rcast_sub, smul_sub]; exact hx.sub hy

-- weighted bound form (only evaluations where spill ≠ 0)
def outlay (a:ℝ)(x:Cover):ℝ:=1+a*area x
private lemma likely_pace (A:Poses L a F w s)(x:E4)(S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i): Likely L fun i=> spill c s (a i) (fun j=>F j i) (mark (a i) x):= by
  unfold spill; refine Likely.sub (Likely.const ..) (Likely.sum _ _ fun j hj=>?_); have ht:= fence L _ _ (marks x S he) (A.payment j hj); refine ⟨_,(Complex.continuous_ofReal.continuousAt.tendsto.comp (c.continuous.continuousAt.tendsto.comp ht)).congr' (he.mono fun i hi=> (if_pos hi).symm)⟩
def Tribes (L:Filter ι)(a:ι→ℝ)(s:Finset I)(F:I→ι→Cover)(w:I→E4)(A:ι→Trace.Contact G): Prop :=
  (∀ p:Fee G,∃ C:ℝ,0≤C∧∀ᶠ i in L,∀ x:Cover, spill c s (a i) (fun j=>F j i) x≠0→ ‖Trace.probe (displace x p.line) (A i)‖≤ C * a i^p.cost * (outlay (a i) x)⁻¹^2) ∧ ∀ y,porch s w y→ Sees L a (fun i=> mark (a i) y) A

lemma ticket_spill (Z:Cleared c w s)(B:Poses L a F w s)(p:Fee G) (S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i) (j:I)(hj:j∈s):Tribes c L a s F w (fun i=>bake (Calling (F j) a p i)):=by
  let G' i:= Calling (F j) a p i; have Ht:=c.rOut_pos
  constructor
  · intro v; obtain ⟨C,hC,H⟩:= Tide.line_receipt v.due (advertised _ p.line p.due); set k:= v.cost+p.cost; set m:=k-2; set b:= c.rIn/2; have hb:0<b:=half_pos c.rIn_pos; set D:= ‖w j‖+1; have hd: 0≤D:=by unfold D; positivity
    have hu(k: ℕ):0≤b⁻¹^k:=by positivity
    set W:= (1+D+1)/b+1; have hw:0≤W:= by unfold W; positivity
    refine ⟨C*W^2*b⁻¹^m,by positivity,?_⟩
    have he': ∀ᶠ i in L,∀ j∈s,∀ t∈s,j≠t →2*c.rOut≤ ‖actual (a i) (F j i-F t i)‖:= (eventually_all_finset _).mpr (fun i hi=> (eventually_all_finset _).mpr (fun j hj=>by by_cases ht:i=j; simp [ht]; exact ((fence L _ _ (B.payment i hi) (B.payment j hj)).norm.eventually (le_mem_nhds (show 2*c.rOut<‖w i-w j‖ by linarith [Z i hi j hj ht]))).mono fun k hk _=> hk))
    filter_upwards [he, S.eventually (ge_mem_nhds zero_lt_one), he',(B.payment j hj).norm.eventually (ge_mem_nhds (lt_add_one _))] with i hi hz hi' hM x hx; have hY:= walled c (F:=fun j=>F j i) hi' hi hx j hj; let y:= F j i; let m':= area (x-y); set t:= a i; have ht:0<t:=hi; have Hm:0<m':=included _; have hP:b≤t*m':=by unfold b m' area; let s:=F j i; nlinarith
    have hₐ: outlay t x ≤ W*(t*m'):=by
      unfold outlay; have hw: area x≤m'+reach y:=by
        unfold area m'; simp_rw [area]; have he:(reach x:ℝ)≤ (reach (x-y):ℝ)+reach y:=by exact_mod_cast (sub_add_cancel x y ▸ Sail.tree (x-y) y)
        linarith
      have hh: t*↑(reach y) ≤ D := (Shade.size_actual hi y).1.trans hM; unfold W; field_simp; nlinarith [mul_le_mul_of_nonneg_left hP hd, mul_le_mul_of_nonneg_left hh hb.le, mul_le_mul_of_nonneg_left hw (show 0 ≤ t*b by positivity)]
    change ‖Trace.probe _ (bake ((t⁻¹^p.cost) • _))‖ ≤ _; rw [map_smul,map_smul,norm_smul,Real.norm_of_nonneg (by positivity : 0≤t⁻¹^p.cost)];
    change t⁻¹^p.cost * ‖handshake (displace x v.line) (displace y p.line)‖ ≤_
    conv_lhs=> rw [show x=y+(x-y) by abel, ← displacement, meter_serves]
    refine (mul_le_mul_of_nonneg_left (H (x-y)) (by positivity : 0≤t⁻¹^p.cost)).trans ?_; rw [show 2+p.k+v.k=v.cost+p.cost by unfold Fee.cost; omega,carry_cost];
    have hk : k=m+2:=by unfold m k Fee.cost; omega
    have h₁ : (t*m')⁻¹ ≤ b⁻¹ := by gcongr
    have hp:0<outlay t x:=by unfold outlay; positivity [included x]
    have h₂:(t*m')⁻¹≤ W / outlay t x:=(le_div_iff₀ hp).2 (by rw [inv_mul_le_iff₀ (show 0<t*m' by positivity)]; simpa only [mul_comm _ W] using hₐ)
    calc
       _ = C*t^v.cost *((t*m')⁻¹^m * (t*m')⁻¹^2):=by rw [← pow_add, ← hk]; unfold k; change t⁻¹^p.cost*(C*(m'^(v.cost+p.cost))⁻¹)=_; rw [inv_pow,inv_pow,mul_pow,pow_add t]; field_simp
       _ ≤ C*t^v.cost*(b⁻¹^m*(W/outlay t x)^2):=by gcongr
       _ = _:=by unfold t; rw [div_eq_mul_inv]; ring
  intro y hy p'; let x i:=mark (a i) y; have hx:= paid_pair p'.due (advertised _ p.line p.due) (show y-w j≠0 from sub_ne_zero.mpr (Ne.symm (hy _ hj))) (fence L _ _ (marks y S he) (B.payment j hj)) he S
  refine ⟨_,(Complex.continuous_ofReal.continuousAt.tendsto.comp hx).congr fun i=>?_⟩; dsimp only [comp]; rw [leg_test]; change ((((a i)⁻¹^(2+p.k+p'.k)*handshake (displace (x i-F j i) p'.line) p.line :ℝ)):ℂ)= ((↑(a i):ℂ)⁻¹)^_ * ↑(handshake (displace (x i) _) (G' i)); unfold handshake G' Calling; simp_rw [map_smul,smul_eq_mul, Complex.ofReal_mul, ← Complex.ofReal_inv, ← Complex.ofReal_pow,← Complex.ofReal_mul]; apply congr_arg ((↑):ℝ→ℂ); rw [show 2+p.k+p'.k=p'.cost+p.cost by unfold Fee.cost; omega,pow_add,mul_assoc]; change _*( _ * handshake (displace _ _) _)= _* (_ * handshake (displace _ _) _); congr 2; rw [show x i=F j i+(x i-F j i) by abel,← displacement,meter_serves]; congr 2; abel
variable (s F w)
def outside : Club G ι where
  carrier := {p|Tribes c L a s F w p}
  zero_mem':=⟨fun _=> ⟨0,le_rfl, Eventually.of_forall fun i x _=> by simp⟩,fun _ _=> silence⟩
  add_mem' := by
    intro X Y hx hy; refine ⟨fun i=>?_,fun i h=> applies (hx.2 i h) (hy.2 i h)⟩; obtain ⟨C,hC,H⟩:= hx.1 i; obtain ⟨D,hD,K⟩:=hy.1 i; refine ⟨C+D,add_nonneg hC hD,?_⟩; filter_upwards [H,K] with j hj hh x ht; rw [Pi.add_apply,map_add,add_mul,add_mul]; exact (norm_add_le ..).trans (add_le_add (hj _ ht) (hh _ ht))
  smul_mem' := by
    intro k X hx; refine ⟨fun i=>?_,fun i h=> quieter k (hx.2 i h)⟩; obtain ⟨C,hC,H⟩:=hx.1 i; refine ⟨‖k‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩; filter_upwards [H] with j hj x ht; rw [Pi.smul_apply,map_smul,norm_smul,mul_assoc ‖k‖,mul_assoc ‖k‖]; exact mul_le_mul_of_nonneg_left (hj x ht) (norm_nonneg _)
-- payment closure
lemma split_issued {v u: ι→Cover→ℂ}(h:Issued L v)(k:Issued L u): Issued L (v+u):=by
  refine ⟨(h.1.and k.1).mono (fun _ hk=> hk.1.add hk.2), (h.2.add k.2).congr ((h.1.and k.1).mono fun i hi=>?_ )⟩; exact (Summable.tsum_add hi.1 hi.2).symm
lemma buy_issued {v:ι→Cover→ℂ}{k:ι→ℂ}(h:Issued L v)(K:Likely L k): Issued L (fun i x=> k i*v i x):=⟨h.1.mono (fun _ hh=> hh.mul_left _), (K.mul h.2).congr (Eventually.of_forall fun i=> (tsum_mul_left ..).symm)⟩
def Jupiter (L: Filter ι) : Accepts ι Cover where
  carrier:={p|Issued L p}
  zero_mem' := ⟨Eventually.of_forall (fun _=> summable_zero), show Likely L _ from ⟨0,by simpa using tendsto_const_nhds (f:=L) (x:=(0:ℂ))⟩⟩ -- synt
  add_mem' :=fun A B=>split_issued A B
  smul_mem' t _ H:=buy_issued H (Likely.const L t)
lemma permits_all : Permit L (Jupiter L):=fun _ ht _ hp=> buy_issued ht hp

variable {s F w} (H: Poses L a F w s) (S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)
def tax (x:E4):ℝ:= (1+‖x‖)⁻¹^6
lemma paid : Integrable tax := by
  have he: (tax : E4→ℝ)= fun x=>(1+‖x‖)^(-(↑(6:ℕ):ℝ)):= funext fun x=> by unfold tax; rw [Real.rpow_neg (by positivity : 0≤ 1+‖x‖),Real.rpow_natCast,inv_pow]
  rw [he]; apply integrable_one_add_norm; norm_num [E4,Axis]
private lemma uniform_spill (p:ℝ)(s:Finset I)(x:I→Cover)(y):‖spill c s p x y‖≤1+s.card:=by unfold spill; apply (norm_sub_le ..).trans; rw [norm_one]; gcongr; exact (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=> (1:ℝ)) (fun i _=> pace_le c _ _)).trans_eq (by simp))
lemma out_cost (b:ℝ)(h:0<b)(x:E4): let t:=outlay b (mark b x); t>0∧1+‖x‖ ≤ 4*t :=by
  intro t; let z:=mark b x; have hv:=current b h x; have he:= Drama.included z; have h₁:t=1+b*area z:=rfl; constructor
  · rw [h₁]; positivity
  have hh:= norm_sub_norm_le x (actual b z); rw [norm_sub_rev] at hh; have hx:‖actual b z‖ ≤2*b* reach z:=(Shade.size_actual h z).2; change ‖actual b z-x‖≤_ at hv; unfold area at h₁; nlinarith [Nat.cast_nonneg (reach z) (α:=ℝ)]
lemma book_ext {A:ι→Trace.Contact G}(p:Word G)(X:Tribes c L a s F w A) (y:E4)(h:porch s w y): Likely L fun i=> (tick a i (debt p))*pit (A i) (Trace.volume (mark (a i) y) (story p)):=by
  induction p with
  | nil=> simp [tick,debt]; exact Likely.const ..
  | cons i p ih=> simp_rw [inc,read_word,map_mul,rings]; simp_rw [show ∀ x, tick a x (i.cost+debt p) =tick a x i.cost * tick a x (debt p) from fun _=>pow_add ..]; exact ((X.2 y h i).mul ih).congr (Eventually.of_forall fun i=> mul_mul_mul_comm ..)
include he in
private lemma bound_ext {A:ι→Trace.Contact G} (p:Word G)(X:Tribes c L a s F w A) : ∃ C:ℝ,0≤C ∧ ∀ᶠ i in L,∀ y:Cover, spill c s (a i) (fun j=> F j i) y≠0→ ‖pit (A i) (Trace.volume y (story p))‖ ≤ C * a i ^ (debt p)*(outlay (a i) y)⁻¹^(2*p.length):=by
  induction p with
  | nil=> exact ⟨1,by simp, Eventually.of_forall fun i x _=> by simp [debt]⟩
  | cons i p ih=>
    obtain ⟨C,hC,H⟩:= X.1 i; obtain ⟨D,hD,V⟩:=ih; refine ⟨C*D,mul_nonneg hC hD,?_⟩; filter_upwards [he,H,V] with j hp hi hh x ht; rw [read_word,map_mul,map_mul,norm_mul,rings,leg_test,Complex.norm_real]; apply (mul_le_mul (hi _ ht) (hh _ ht) (norm_nonneg _) (by positivity)).trans_eq; rw [inc,pow_add,List.length_cons,mul_add, mul_one,pow_add]; ring
variable [L.IsCountablyGenerated] {A:ι→Trace.Contact G}
private def motion (a:ι→ℝ)(i:ι)(F:I→ι→Cover)(s:Finset I)(p: Chart2.St ℤ G)(x:Cover):= spill c s (a i) (fun j=> F j i) x • Trace.volume x p
include he H S in
lemma tax_pay (T:Tribes c L a s F w A) {p: Chart2.St ℤ G}(h:p∈ Mu.throne G 3 4): Issued L (fun i x=> pit (A i) (motion c a i F s p x)):=by
  induction h using Submodule.span_induction with
  | mem p h=>
    obtain ⟨p,ht,rfl⟩:=h; have hh:p.length=3∧ debt p=4:=ht; let q i x:= pit (A i) (motion c a i F s (story p) x)
    obtain ⟨C,hC,Hc⟩:= bound_ext c he p T; let C' := (1+(s.card:ℝ))*C* (4:ℝ)^6; have hp:= fun (x:E4) (hx:porch s w x)=> book_ext c p T x hx; apply speeds q he (Stall.paid.const_mul C') ?_ ?_
    · filter_upwards [he,Hc] with i hi hv; refine Eventually.of_forall fun x=>?_ ; let f:=a i; let y:=mark (a i) x; set B:=outlay f y; let z:= spill c s f (fun j=> F j i) y; obtain ⟨hb,hw⟩:=out_cost f hi x; change ‖(f:ℂ)⁻¹^4 * pit (A i) (z • _)‖≤ _; rw [norm_mul,map_smul,norm_smul]; rw [norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg hi.le]
      by_cases hz:z=0; rw [hz,norm_zero,zero_mul,mul_zero]; unfold C' tax; positivity
      refine (mul_le_mul_of_nonneg_left (mul_le_mul (uniform_spill ..) (hv _ hz) (norm_nonneg _) (?_)) (?_)).trans ?_ -- edit
      · positivity
      · positivity
      rw [hh.1,hh.2]; change f⁻¹^4 * ((1+(s.card:ℝ))*(C*f^4* B⁻¹^(2*3)))≤ _
      calc _= (1+(s.card:ℝ))*C * B⁻¹^6:= by have hf:0<f:=hi; have hh:0<B:=hb; rw [show 2*3= (6:ℕ) from rfl]; field_simp
           _ ≤ _:=  by
            unfold C' tax; rw [mul_assoc ((1+(s.card:ℝ))*C),← mul_pow]; have hh:0<B:=hb; gcongr _ * (?_^(6:ℕ)); rw [inv_le_iff_one_le_mul₀ hh]; have ht:0<1+‖x‖:=by positivity
            field_simp; exact hw
    have hE:∀ j:I,∀ᵐ x:E4,w j≠x:= fun j=> mem_ae_iff.mpr (by change MeasureTheory.volume ({x:E4| w j ≠ x}ᶜ)=0; rw [show ({x|w j ≠ x}ᶜ : Set E4)={w j} from Set.ext fun i=>by simp [eq_comm]]; simp)
    filter_upwards [(eventually_all_finset s).mpr (fun j _=> hE j)] with x hx
    specialize hp x hx; rw [hh.2] at hp; refine ((likely_pace c H x S he).mul hp).congr (Eventually.of_forall fun i=>?_); unfold q motion; simp only [steps,map_smul]; change _*( (a i:ℂ)⁻¹^4 * _)=(a i:ℂ)⁻¹^4*(_*_); exact mul_left_comm ..
  | zero=> simp_rw [motion,map_zero,smul_zero,map_zero]; exact (Jupiter L).zero_mem
  | add p q _ _ i j=> simp only [motion, map_add, smul_add]; exact split_issued i j
  | smul u p _ i=> simp_rw [motion,map_smul,smul_comm _ u,smul_eq_mul]; unfold motion at i; simp_rw [map_smul,smul_eq_mul] at i; exact buy_issued i (Likely.const L u)
include S H he in
theorem ticket_out (j:PlaqAxes)(Z:Cleared c w s)(x:I→ι→Mu.Stamp G)(H':∀ j∈s,Records a L (F j) (x j)): Issued L (fun i v=> spill c s (a i) (fun j=> F j i) v * E (Mu.root G) (V3 G (v,j)*web s x i)) :=by
  classical
  let K:Club G ι:= outside (L:=L) c s F w (a:=a); let p:Mu.Stamp G:= V3 G ((0:Cover),j); let P (i:ι):= motion c a i F s p
  have hK: Shops a L K F s:=⟨fun i hi j hj hn q p _ _=> position_pay _ _ (H.payment i hi) (H.payment j hj) (fun p=> hn (H.ends hi hj p)) S he,fun i hi v hv=>ticket_spill c Z H v S he i hi⟩
  have hp: Admits (Jupiter L) K P:=by obtain ⟨n,hn⟩:= degreeAny p; exact ⟨⟨n,fun i x=>(DegZ _ n).smul_mem _ (name_charge hn (Trace.radius x))⟩,fun q h=> tax_pay c H S he h (stationed (G:=G) ((0:Cover),j))⟩
  rw [show (fun i v=> spill c s (a i) (fun j=>F j i) v* E (Mu.root G) (V3 G (v,j)*web s x i))=hall s x P from ?_ ]; exact pays (Jupiter L) _ hK permits_all _ H' _ hp
  funext i v; unfold hall P motion; rw [map_smul, ← show V3 G (v,j)=_ from encoded v j,← show flicker (V3 G _) = _ from opens_V (G:=G) (v,j)]; rw [came,opens_V,smul_mul_assoc,map_smul]; rfl
end YM.XSpace.Stall
