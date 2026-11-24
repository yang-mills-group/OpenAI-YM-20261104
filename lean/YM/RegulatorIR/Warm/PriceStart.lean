import YM.RegulatorIR.Warm.Harvest

/-!
# All common valuation power budgets at top. Contributions stamped
*before* identifying the carrier normalization. Scale β rest valued by
its matching degree, even when legs filtered. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Warm
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {G:Gauge}{X Y:Type}{s m p e j r:ℕ}{n:Side}

variable (S:Scale) {T:Face ℤ→ Orders (Foot G)}
local notation "L"=> Clocks.flat
def beginF (G:Gauge) (z:Face ℤ) : Orders (Foot G) := ((boons G L z).some.issues (-1) 0).choose
lemma always (G:Gauge)(z:Face ℤ) : Lab 0 (-1) (plain L G z) (beginF G z) := ((boons G L z).some.issues _ _).choose_spec
-- use other term helper from Hear
lemma no_one (G:Gauge)(z:Face ℤ) : beginF G z 1=0:=by
 let F:= beginF G z
 have hp:= always G z
 refine guessed (hp.scope_ _) (fun i hi=> False.elim (hi rfl)) (hp.smooth _) (fun _=> symmetric_zero) ?_
 intro i; let M:= flank (plain L G z) i
 have h : coeff 1 (tale M)=0:= Clocks.grows_sq (f:=M) ((boons G L z).some.smooth_v _) (fun _=> mul_nonneg ((L).forward _) (G.price_range ..).1) (by unfold M flank;rw [zero_smul]; exact plain_rest _ _ _ _) _ (by omega)
 rw [hp.figures i (by decide),show coeff _ _= _ from h,mul_zero];simp [drums,strum]

lemma correlate (v:ℝ)(F:ℝ→ℝ)(h:ContDiffAt ℝ ∞ F 0) (e:ℕ): coeff e (tale (fun x:ℝ=> F (x*v)))= v^e*coeff e (tale F):=by
 rw [show tale (fun x:ℝ=> F (x*v))=inscription F v from Prim.lore h v,tale_jet, Binding.inscription, PowerSeries.coeff_mk]
 nth_rw 1 [← mul_one v]; exact jet_smul ..
lemma positionS (F:Micro X)(H:Orders X)(c:ℝ)(hp: Lab 0 c F H)(hr:∀ i j,F i=F j)(hh:Nonempty (Run F)) (p i:ℕ)(h:i≠p) : H p i=0:=by
 let V:= H p; have hv: Within p V:= hp.scope_ _
 by_cases he:i∈ Finset.range (p+1); swap;exact Classical.not_not.mp fun h'=>he (mem_range.mpr (Nat.lt_succ_of_le (hv _ h')))
 cases Nat.eq_zero_or_pos p with
 | inl t=> subst p; rw [hp.awake];rfl
 | inr t=>
   have hx (w:X→ℝ) (y:ℝ) : drums V p (y • w)=y^p*drums V p w:=by
      have hv(s : X→ℝ): drums V p s=c*coeff p (tale (flank F s)):=hp.figures s t
      rw [hv,hv,show flank F (y • w) = (fun t:ℝ=> flank F w (t*y)) from ?_,correlate y (flank F w) (hh.some.smooth_v w) p];ring
      funext i; unfold flank; rw [smul_smul]; exact congr_fun (hr i (i*y)) _
   let P k:= if h:k=p then h.symm ▸ V p else (0:Packet (X) k)
   have he(v): strum (V i) v=0:= by
      have ht:= ext_power (fun i=>strum (V i) v) (fun i=> if i=p then drums V p v else 0) (Finset.range (p+1)) (fun k=>?_) he -- ext_power args includes i
      rw [if_neg h] at ht; exact ht
      rw [sum_eq_single_of_mem (f:=fun i=>k^i*(if i=p then drums V p v else 0)) p (by simp),if_pos rfl,← hx,drums]; apply sum_congr rfl; intro _ _;exact (strum_v ..).symm
      intro b _ h; rw [if_neg h,mul_zero]
   let S(j):Packet (X) j:= if j=i then 0 else V j
   have hz: V=S:=by
       apply guessed hv (by intro j hj;unfold S at hj; split at hj; contradiction; exact hv _ hj) (hp.smooth p) (by intro j; unfold S; split; exact symmetric_zero; exact hp.smooth p j)
       intro x; unfold drums;apply Finset.sum_congr rfl;intro j _; by_cases hh:j=i
       · subst j; rw [show S i=0 from if_pos rfl,strum_zero];exact he x
       rw [show S j=V j from if_neg hh]
   change V i=0;rw (occs:=.pos [1]) [hz];exact if_pos rfl
lemma placed (x:Face ℤ)(G:Gauge) (p i:ℕ)(h:i≠p) : beginF G x p i=0:= positionS _ _ _ (always G x) (fun _ _=>rfl) (boons G L x) p i h
-- linear decomp without bias_hi implicit own.
variable (H:Plane S G T)
include H
lemma plain_fee (x: Face ℤ)(he:0<e): T x e=laterBias S e (beginF G x):=by
 let V:= beginF G x; have hp:= H x;have ht:=always G x; let f:= antidiagonal (e+2);let k:=antidiagonal e;let φ:=fun (d:ℕ×ℕ)=> biases S d.1 • V d.2
 have h : (∑ d∈f,φ d) = laterBias S e V:=by
    unfold laterBias; symm;let t:=fun z:ℕ×ℕ=> (z.1,z.2+2);apply Finset.sum_of_injOn t
    · intro i _ j _ h; obtain ⟨p,hv⟩:=Prod.mk.inj h; exact Prod.ext p (add_right_cancel hv)
    · intro i hi; exact mem_antidiagonal.mpr (show i.1+(i.2+2)=e+2 from by have h:= mem_antidiagonal.mp (show i∈ k from hi);omega)
    · intro i hi h; by_cases he:2 ≤ i.2
      · have hy:(i.1,i.2-2)∈k:=by rw [mem_antidiagonal]; have hp:= mem_antidiagonal.mp (show i∈f from hi);simp only;omega
        have hg:t (i.1,i.2-2)=i:= Prod.ext rfl (Nat.sub_add_cancel he)
        exact (h ⟨_,hy,hg⟩).elim
      have hh:i.2=0 ∨ i.2=1:=by omega
      unfold φ; obtain hh|hh:=hh;rw [hh, show V 0= _ from ht.awake,smul_zero]; rw [hh,show V 1= _ from no_one G x,smul_zero]
    intro i hi; rfl
 rw [← show _=laterBias S e (beginF G x) from h]
 apply guessed (hp.scope_ _)
 · intro i hi;rw [Finset.sum_apply] at hi; obtain ⟨w,hw,h⟩:= exists_ne_zero_of_sum_ne_zero hi; have hZ: V w.2 i≠ 0:=fun hz=> h (by change biases S w.1 • V w.2 i=_;rw [hz,smul_zero]); have hr:=ht.scope_ _ _ hZ; have hx:= mem_antidiagonal.mp hw;omega
 · exact hp.smooth _
 · intro i;rw [Finset.sum_apply];exact symmetric_sum fun j _=> symmetric_scale (ht.smooth _ _) _ -- args
 intro v; rw [hp.figures v he,Oracle.earned_drums]
 swap; exact fun j _ k=> sB _ (ht.sized j.2 k) _
 let F:=flank (plain L G x) v
 have he : flank (plain S G x) v=S.beta*F:=by ext1 i; change S.beta i*_ = _*(1* _);rw [one_mul]
 rw [he,tale_mul S.near ((boons G L x).some.smooth_v _),PowerSeries.coeff_mul,mul_sum]; apply sum_congr rfl; intro i hi; have hx:= mem_antidiagonal.mp hi
 unfold φ;rw [drums_scale]; change _= biases S i.1*_; by_cases he:i.2=0
 · rw [he, show V 0=0 from ht.awake, tale_base]; have hF: flank (plain L G x) v 0=0:=by unfold flank; rw [zero_smul,plain_rest];
   simp [hF,drums,Prim.strum]
 rw [← hardy (V i.2) (ht.scope_ _),show drums _ _ _= _ from ht.figures v (Nat.pos_of_ne_zero he)]; exact mul_left_comm ..
 omega
lemma primary_low (he:0<e)(hr:r<2) : many T e r=0:=by
 ext1 v; change (∑' x,T x e r v)=(0:ℝ); simp_rw [plain_fee S H _ he,laterBias,Finset.sum_apply]; rw [← tsum_zero (β:=Face ℤ) (α:=ℝ)];apply tsum_congr; intro x; apply sum_eq_zero;intro i _
 change biases S i.1*beginF G x (i.2+2) r v=0; rw [placed _ _ _ _ (by omega)]; exact mul_zero _
lemma primary_high (he:0<e)(hr:2 ≤ r)(hi:r ≤ e+2) : many T e r = biases S (e+2-r) • (many (beginF G) r r):=by
 have hx(x) : T x e r=biases S (e+2-r) • beginF G x r r:=by
    rw [plain_fee S H _ he,laterBias,Finset.sum_apply,sum_eq_single_of_mem (e+2-r,r-2) (by rw [mem_antidiagonal];dsimp only;omega)]; change biases S _ • beginF G x _ r= _;rw [Nat.sub_add_cancel hr]
    intro i hx hh
    change biases _ _ • beginF G x (i.2+2) r=_;rw [placed,smul_zero]
    intro h; have hq:=mem_antidiagonal.mp hx;apply hh;exact Prod.ext (by change i.1=e+2-r;omega) (by change i.2=r-2;omega)
 ext1 v; change (∑'x,T x e r v)=biases _ _*_ ;simp_rw [hx,Pi.smul_apply,smul_eq_mul,tsum_mul_left]; rfl
end YM.RegulatorIR.Warm
