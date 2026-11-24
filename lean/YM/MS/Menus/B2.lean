import YM.MS.Menus.Policy
/-!
# Taylor transport B₂ tensor

Use true physical signs with ghost-axis roles. One `Plan` entry. Extend through
 powers and weight charts. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost Detect Detect.Mark Wire
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open PowerSeries (coeff)
open Complex (I)
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} (p:Team)(x:ℝ) (u v: Polynomial ℝ){k:ℕ}

lemma θ2 (i j:Branch G Axis)(w:FourP)(x:ℝ)(hk:0<k):
   Tone.run (style G p x k-style G (rush p u v k) x k) [(i,w),(j,-w)]=matchA i.2 j.2 (kinds (2*u.eval x) (v.eval x-u.eval x) i.1 j.1 (wave w)) := by
    rw [rush_diff x hk, map_sub, Pi.sub_apply]; simp_rw [train2]; rw [← sub_mul]; simp_rw [show run (G:=G) (core G 0) [(i,w),(j,-w)]=_ from rankTwo w i j] -- pulse
    let W:=rush p u v k; let P (a:Atom Axis):= coeff k (adap p a x)-coeff k (adap W a x)
    rw [expansion]; swap; · exact fun i hi=>rushed hi
    swap; · exact hk
    have ha (i:Axis): P (some i,false)= -(↑(u.eval x):ℂ):= EQ_A x hk i p
    have hT (i:Axis): P (some i,true)= ↑(u.eval x) := by
          let he := tweak x (p:=p) (q:=W) (fun _ h=>rushed h) hk (some i); unfold P; rw [he,← neg_sub, show coeff k (adap p _ _) -_ =_ from ha i, neg_neg]
    have hc : P (none,false)= -(↑(v.eval x):ℂ):= EQ_C x hk p
    change (P i.1+P j.1)*styleK w i j = _
    rcases i with ⟨⟨_|i,_|_⟩,t⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,s⟩ <;> unfold styleK matchA
    all_goals by_cases hx:t=s <;> simp only [hx,↓reduceIte,mul_zero,ha,hc,hT,kinds,α₂,μ2,zero_add,add_zero];
    all_goals first| rfl|(push_cast; ring)
lemma Rpair (u v:ℝ) (i j: Branch G Axis)(w:FourP) : Rest (fun t:ℝ=> matchA i.2 j.2 (kinds u v i.1 j.1 (wave (t • w)))) (4-(wfield i + wfield j)) (ranktwo u v [(i,w),(j,-w)]):= by
    rcases i with ⟨i,a⟩; rcases j with ⟨j,t⟩; unfold matchA; by_cases h:a=t; swap; · simp [h,ranktwo]; exact Rest.zero _
    simp only [if_pos h,ranktwo]; rcases i with ⟨_|i,_|_⟩ <;> rcases j with ⟨_|j,_|_⟩ <;>
     first| exact Rest.zero _| exact (waveFormR w i).smul (_*I)| exact (waveFormR w j).smul (_*I)| skip
    unfold kinds; simp_rw [mul_comm _ (u:ℂ)]; exact (baseK w i j).smul _

lemma ranktwo_off (u v:ℝ) (w:List (Lane4 G))(h:w.length≠2): ranktwo u v w=0:=by rcases w with _|⟨_,_|⟨_,_|a⟩⟩ <;> first| rfl| exact (h rfl).elim
lemma scale_car (hk:0<k): Career G p (rush p u v k) k 2 4 (fun x=>ranktwo (2*u.eval x) (v.eval x-u.eval x)):= by
    refine ⟨fun i H=>rushed H, fun x=>?_, fun x=>?_⟩; · rw [rush_diff x hk]; exact (merited (Y p x) (core G 0) (k:=k) (participates G 0)).sub (merited (Y _ _) _ (k:=k) (participates G 0))
    intro w hw; by_cases he:w.length=2; swap; · rw [show fieldVal _ (ray w)=fun _=>(0:ℂ) from funext fun i=> strange (sail (ray w) i) (by simp; omega), ranktwo_off _ _ w he]; exact Rest.zero _
    obtain ⟨⟨i,w⟩,⟨j,r⟩,rfl⟩:= List.length_eq_two.mp he; obtain rfl : r= -w:= by simpa [net, add_eq_zero_iff_eq_neg', eq_comm] using hw rfl -- equality reverses substitution choose tactic?
    unfold fieldVal; simp only [ray_go,List.map_cons, List.map_nil]; simp_rw [show ∀ x y:Mode (Branch G Axis) QP,∀ f:Law G, Book.mask (2:ℕ) f [x,y]=f [x,y] from fun x y f=> enough _ (by simp), smul_neg, θ2 p u v i j _ x hk]; rw [show fieldDim wfield [(i,w),(j,-w)]= wfield i+wfield j by simp]; exact Rpair ..
lemma buys_pair {P Q:ℝ→ℝ} (h:1≤k)(hp:Ready P)(ht:Ready Q): ∃ q, Career G p q k 2 4 (fun i=> ranktwo (P i) (Q i)) := by
   obtain ⟨u,rfl⟩:= hp.scalar; obtain ⟨v,rfl⟩:= ht.scalar; let T:Polynomial ℝ:= Polynomial.C (2:ℝ)⁻¹*u; let S:= T+v; refine ⟨rush p T S k,?_⟩; convert scale_car (G:=G) p T S h using 2; ext x; simp [T,S] -- inspect
end YM.MS.Menus
