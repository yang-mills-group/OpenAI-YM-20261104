import YM.FVA2.Position.Echo
import YM.MS.Motif.K2
import YM.MS.Motif.Warp

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.OpenAxis
open Function Set Filter Finset
open MS MS.Plane MS.Koszul MS.Motif MS.Arts MS.Halo
open MS.Landau MS.Landau.Detect MS.Book MS.Momentum
open Analysis Tensor Maxwell Labels MS.Theater
open InnerProductSpace
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {G:Gauge} {m n h:ℕ} {x:E4} {a b c:Axis} {p:FourP}
local notation "↓"=> Tensor.diagonal
def leadC (X: Feet G (h+1))(i j:Axis)(x:E4): G.Color:= grad i (↓ (X.val j)) x- grad j (↓ (X.val i)) x
lemma lead_value (X: Feet G (h+1))(i:Axis)(x:E4): ((h:ℝ)+2) • (yard G h X).value i x=∑ j:Axis,x j • leadC X j i x:= by
 let A a x := ↓ (X.val a) x; let r:ℝ := h+1
 let f:= ↓ (( gradS G (h+1) (radialX _ (h+1) X ) ).val i ) x
 have he: f= A i x + ∑ j:Axis,x j • grad i (A j) x:= by
    change (↓ ((stepL G Unit (h+1) i (radialX G (h+1) X)).val ())) x=_; unfold stepL; rw [workL,funext (tBudget X)]; exact grad_self ..
 unfold leadC; simp_rw [smul_sub, Finset.sum_sub_distrib,grad_euler (X.val i) (X.property i)]; push_cast; rw [Theater.projectionY,carveΩ]; change _ • ( A i x-( divYear _ )⁻¹ • f)=_; simp only [ divYear,Nat.cast_add,Nat.cast_one,add_assoc ]; rw [show (1+1:ℝ)=2 from (by norm_num)]; simp_rw [smul_sub]; rw [smul_inv_smul₀ (by positivity: (h:ℝ)+2≠0),he]; simp only [ add_smul,two_smul,one_smul]; unfold A; abel
abbrev lampX (x:E4)(p:FourP):ℝ:= inner ℝ ( fixF p ) x
lemma beam_p (p:FourP)(x:E4): ∑ i:Axis,x i * p i= lampX x p:= by unfold lampX; rw [PiLp.inner_apply]; exact sum_congr rfl fun i _=>rfl
lemma depthV (X:Feet G (h+1))(a b:Axis)(x:E4): grad b (↓ ( X.val a )) x=↓ ((stepL G Axis h b X).val a) x:= congr_fun (workL (basis b) X a).symm _
lemma lead_1 (p:FourP)(v:G.Color)(x:E4)(a j:Axis): ↓ ((speak h a p v).val j) x= if j=a then ((Nat.factorial h:ℝ)⁻¹*(lampX x p)^h) • v else 0:= by
 classical
 split; · next h=> subst j; rw [speak,Tensor.diagonal,wearing]; simp only [ Finset.prod_const,Finset.card_univ,Fintype.card_fin ]; exact (mul_smul ..).symm
 next hv=> rw [speak,away h (fixF p) v hv,Tensor.diagonal,zero_apply]
lemma lead_2 (p:FourP)(v:G.Color)(x:E4)(k a b:Axis): leadC (speak (h+1) a p v) k b x=((Nat.factorial h:ℝ)⁻¹*(lampX x p)^h) • ((polar0 (n:=0) k b a p) • v) := by -- polar0 defs axis index type inference
 unfold leadC; rw [depthV,depthV,step_at,step_at]; change (p k) • (↓ ((speak h _ _ _).val b) x) - (p b) • (↓ ((speak h _ _ _).val k) x)=_; rw [lead_1,lead_1]; unfold polar0 Landau.delta; by_cases hv:k=a <;> by_cases ht:b=a <;> simp [hv,ht] <;> exact smul_comm ..
lemma raw_g (k:ℕ)(u:Shore G 0)(x:E4)(a b:Axis)(i:G.ColorIndex): graft (m:=0) 0 a b x k i [u]= (I* ((lampX x u.2:ℝ):ℂ))^k * cur (n:=0) 0 (chair 0 a) (chair 0 b) i [u]:= by
 induction k with
 | zero=> rw [graft,pow_zero,one_mul]
 | succ k ih=>
    rw [graft]; simp_rw [Finset.sum_apply, Pi.smul_apply,convoke,zero_smul,add_zero, axisP,lock, rowP, moon, net_cons, show net (A:=Cfield G 0) ([]:Legs (Shore G 0))= 0 from rfl,add_zero, spike_δ, spikeV, ih,Complex.real_smul]; rw [← beam_p]; push_cast; simp_rw [Finset.mul_sum]; rw [pow_succ', mul_assoc, Finset.sum_mul]; refine Finset.sum_congr rfl (fun j _=>?_); rw [show chair 0 j=j from rfl]; ring
/-- linear convention also off index `u`, directly at momenta. -/
lemma bright_g (k:ℕ)(i:G.ColorIndex)(a b:Axis)(v:G.ColorIndex)(x:E4)(p:FourP)(r:Axis): graft (m:=0) 0 a b x k i [(at_g (chair 0 r) v,p)]= (Nat.factorial k:ℂ)* hitϑ (k+1)*(↑((leadC (speak (k+1) r p (cl G v)) a b x) i:ℝ):ℂ):= by
 rw [raw_g,cur,zero_smul,add_zero]; simp only [f_ref,lead_2]; unfold cl polar0 hitϑ; simp only [PiLp.smul_apply,smul_eq_mul,EuclideanSpace.single,PiLp.single_apply]; by_cases ht:i=v
 · rw [ht]; simp [show ∀ i, chair 0 i=i from fun _=>rfl]; unfold lampX; have hF:(k.factorial:ℂ) ≠ 0:= (by exact_mod_cast Nat.factorial_ne_zero _); field_simp; ring
 rw [if_neg (Ne.symm ht)]; simp [ht]
lemma eff (i:G.ColorIndex)(x:E4) : rank 1 (graft (m:=0) 0 a b x h i):= by
 induction h with| zero=> rw [graft,cur,zero_smul,add_zero]; exact rank_α _ _ _| succ h ih=> rw [graft]; simp_rw [ Finset.sum_apply,Pi.smul_apply,convoke,zero_smul,add_zero ]; exact Rails.sum _ (fun a _=> (mon_apply ih (Motif.δ (chair 0 a))).smul ( ( x a:ℝ ):ℂ ) )
lemma low_μ (k:ℕ)(p:FourP)(v:G.ColorIndex)(f:Cfield G 0)(H:∀ a c, f≠ at_g a c)(x:E4)(i:Axis) : Ray G 0 k 0 i x v [(f,p)]=0:= by
 unfold Ray; simp only [Pi.smul_apply,Finset.sum_apply, raw_g, cur,zero_smul,add_zero, c_α,H,↓reduceIte,mul_zero,sub_self,smul_zero,Finset.sum_const_zero]
lemma prong_lit (x:E4) (i:G.ColorIndex): Ramp G h (asC G h (Prong a x i)) 0 0= mono (RowLeg G h (asC G h (Prong a x i))):= by
 rw [ramp_Jrad]
 ext l; by_cases hv:l.length=1; swap
 · have he: rank 1 (Ray G 0 h 0 a x i):= by simp only [ Ray,Pi.smul_apply, Finset.sum_apply ]; exact ( Rails.sum _ (fun l _=> (eff i x).smul ( ( x l:ℝ ):ℂ ) ) ).smul (↑( (slotDen h)⁻¹ ):ℂ)
   rw [he l (by rw [mod_int]; omega), grade1 _ l (by rw [mod_int]; omega)]
 obtain ⟨⟨f,p⟩,rfl⟩:= List.length_eq_one_iff.mp hv; by_cases he:∃ a c, f= at_g (n:=0) a c; swap; · rw [low_μ _ _ _ _ (fun a c H=> he ⟨a,c,H⟩)]; rcases f with ⟨⟨_|j,_|_⟩,c⟩ <;> first|rfl| exact (he ⟨j,c,rfl⟩).elim
 obtain ⟨j,c,hc⟩:= he; subst f; simp only [Ray, Finset.sum_apply,Pi.smul_apply]; -- goal read ↓
 let W:= speak (h+1) j p (cl G c); change _= hitϑ (h+1)*(↑((yard G h W).value a x i:ℝ):ℂ)
 have hm := congr_arg (fun c:G.Color=> c i) (lead_value W a x); simp only [PiLp.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,smul_eq_mul] at hm -- verify name
 let y:= (↑((yard G h W).value a x i:ℝ):ℂ); have ht : (∑ t:Axis,( x t :ℂ ) * (↑((leadC W t a x) i:ℝ):ℂ))= ((h:ℂ)+2)*y:= by unfold y; exact_mod_cast hm.symm
 simp_rw [Complex.real_smul]; change _= _*y; rw [ show (∑ t:Axis,_)=( h.factorial:ℂ ) * hitϑ (h+1) * (((h:ℂ)+2)*y) from ?_, slotDen]
 · push_cast; have hH:(h.factorial:ℂ)≠0:= (by exact_mod_cast Nat.factorial_ne_zero _); have hK:( h:ℂ )+2≠0:= (by norm_cast); field_simp -- mixed heights
 · rw [← ht, Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _=>?_ ); unfold W; rw [show j=chair 0 j from rfl,bright_g]; rw [show chair 0 j=j from rfl]; ring
lemma ramps_real (L:Coord G h): Ramp G h (asC G h L) 0 0=mono ( RowLeg G h (asC G h L) ):= by
 obtain he:L∈ Submodule.span ℝ (Samples G h):= by rw [many]; exact Submodule.mem_top
 refine Submodule.span_induction (p:=fun L _=>Ramp G h (asC G h L) 0 0= mono ( RowLeg G h (asC G h L) )) ?_ ?_ ?_ ?_ he
 · rintro _ ⟨a,x,c,rfl⟩; exact prong_lit ..
 · rw [map_zero,map_zero,map_zero]; ext l; rcases l with _|⟨_,_|l⟩ <;> rfl
 · intro f g H K hF hG; simp only [map_add,Pi.add_apply,hF,hG,Koszul.mlin]
 intro c f H hv; rw [map_smul]; simp_rw [show ∀ (x: Witness G h), c • x=(c:ℂ) • x from fun _=>rfl,map_smul,Pi.smul_apply,hv,Koszul.mcost]
end YM.FVA2.Position.OpenAxis
