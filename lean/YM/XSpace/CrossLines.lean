import YM.XSpace.Compat.Episode
import YM.XSpace.ImageSum
import YM.XSpace.Splices
import YM.Next.RANK.Stride

/-!
# Reconciling KP's two-point comparison with operator derivatives

All ordinary periodic cross lines entering leading computations. Genuine
Maxwell-leg normalization, no arbitrary Fourier factor. Pointwise statement in
native spacing units; rescale keeping finite offsets in the next step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Cross
open YM.XSpace.Compat.KP
open Lattice Filter Set Function Exterior Labels Source Source.Drops Maxwell
open Next.Rank Configuration CellsInt Beamer Further.FreeCovariance.KP Top
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {n : Side} {r s j l : ℕ} (R : Period)

-- Endpoint test includes root, use actual lattice coordinates here.
def faceOf (x : Cover) (a : PlaqAxes) : Faces R.side:= (wrap R.side x,a)

def lag (x y : Cover) (i p : Address G) := Bare.direct (faceOf R (x+i.1) i.2.1) (faceOf R (y+p.1) p.2.1) i.2.2 p.2.2
lemma leg_symm (x y : Cover) (i p : Address G): lag R x y i p= lag R y x p i:=Bare.direct_symm ..
lemma lag_spectral (x y : Cover) (u v : Address G): lag R x y u v = if u.2.2=v.2.2 then (fourier R.side u.2.1 v.2.1 ((x+u.1)-(y+v.1))).re else 0 := Bare.direct_lattice _ _ _ _ (map_sub ..)

private lemma winds (A : R.Bonds → G.Color) (x : R.Sites) (i j k : Axis):
    (R.curlIJ A (x+step i) j k - R.curlIJ A x j k) + (R.curlIJ A (x+step j) k i-R.curlIJ A x k i)+(R.curlIJ A (x+step k) i j-R.curlIJ A x i j)=0:=by unfold Period.curlIJ; simp only [add_right_comm x]; abel
private lemma chute (x : Cover) (v : Forms G R.side) (hv : v∈Curled G R.side): shutter (fun p : Address G=> v (faceOf R (x+p.1) p.2.1) p.2.2) :=by
  obtain ⟨u,rfl⟩:=hv
  let g : Horizon G:= fun p=> Top.curl _ _ u (faceOf R (x+p.1) p.2.1) p.2.2
  let A:= collect G u
  have ht (i j p h) : light g i j p h= R.curlIJ A (wrap R.side (x+p)) i j := by
    change WithLp.toLp 2 (fun k : G.ColorIndex => g (p,⟨(i,j),h⟩,k)) = _; apply congr_arg _ (by funext k; change Top.curl G R.side u _ k= _; rw [R.cover_curl]; rfl)
  have he (i j p): Beamer.polar g i j p= R.curlIJ A (wrap R.side (x+p)) i j:= by
    unfold Beamer.polar; split
    · exact ht ..
    split_ifs with hy; rw [R.curlJI,ht]
    rename_i hx; have hp:i=j := le_antisymm (le_of_not_gt hy) (le_of_not_gt hx); simp [hp,Period.curlIJ]
  intro i j k; funext p; change stepValue (Beamer.polar g j k) i p+stepValue (Beamer.polar g k i) j p+stepValue (Beamer.polar g i j) k p = 0
  simp only [stepValue,he,← add_assoc,map_add,wrap_step]; exact winds R A _ i j k
lemma incoming (x y : Cover) (p : Address G): shutter (fun i => lag R x y i p):=by
  let P:= (Curled G R.side).starProjection (unitFace (faceOf R (y+p.1) p.2.1) p.2.2); have he (i : Address G):lag R x y i p=P (faceOf R (x+i.1) i.2.1) i.2.2:= atFace ..
  simp_rw [he]; exact chute R x P (Submodule.starProjection_apply_mem ..)
lemma outgoing (x y : Cover) (p : Address G): shutter (lag R x y p):= by rw [show lag R x y p=fun i=>lag R y x i p from funext (leg_symm R x y p)]; exact incoming R y x p

lemma on_mourn (L M : Module.Dual ℝ (Horizon G)) (hb : bright M) (x y : Cover)
    (u : Reading G j r→ℝ) (H : ∀ f : Horizon G,shutter f→ L f=∑ i,u i*gesture (mood i) f)
    (v : Reading G l s→ℝ) (K : ∀ f : Horizon G,shutter f→ M f=∑ i,v i*gesture (mood i) f):
    mourn L M (lag R x y)=∑ i, ∑ j,u i*v j*mourn (gesture (mood i)) (gesture (mood j)) (lag R x y):=by
  change L (fun i => M (lag R x y i)) = _
  rw [H _ (shut_reader hb _ (incoming R x y))]; apply Finset.sum_congr rfl; intro i _
  rw [show gesture (mood i) (fun i=> M (lag R x y i))=mourn M (gesture (mood i)) (lag R y x) from (moves (gesture (mood i)) M (lag R x y) hb).trans (by simp_rw [leg_symm R x y])]
  rw [show mourn M (gesture (mood i)) (lag R y x)= M (fun k=>gesture (mood i) (lag R y x k)) from rfl, K _ (shut_reader (bright_gesture _) _ (incoming R y x)),Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_
  rw [mul_assoc,show gesture (mood j) (fun k => gesture (mood i) (lag R y x k))=mourn (gesture (mood i)) (gesture (mood j)) (lag R x y) from (moves (gesture (mood j)) _ (lag R y x) (bright_gesture (mood i))).trans (by simp_rw [leg_symm R y x])]

-- KP difference conventions
section
variable (t : Fin j → Axis) (F : Cover → ℂ)
private lemma paid_step (p q w : Cover) : jumps j t (fun z => (F (p+z-q)).re) w = (slot checkin (List.ofFn t) F (p+w-q)).re:=by
  induction j generalizing F with
  | zero=>rw [List.ofFn_zero];rfl
  | succ j ih =>
    rw [List.ofFn_succ, jumps,slot]; apply Eq.trans _ (ih (Fin.tail t) (checkin (t 0) F)); congr! 2 with z; unfold stepValue checkin; simp only [Complex.sub_re]; rw [show p+(z+step (t 0))-q=p+z-q+step (t 0) by abel]
private lemma paid_neg (p q w : Cover) : jumps j t (fun z => (F (p-(q+z))).re) w=(slot checkout (List.ofFn t) F (p-(q+w))).re:=by
  induction j generalizing F with
  | zero=>rw [List.ofFn_zero];rfl
  | succ j ih=> rw [List.ofFn_succ,jumps,slot]; apply Eq.trans _ (ih (Fin.tail t) (checkout (t 0) F)); congr! 2 with z; unfold stepValue checkout; simp only [Complex.sub_re]; rw [show p-(q+(z+step (t 0)))=p-(q+z)-step (t 0) by abel]
end
lemma matched_mourn (x y : Cover) (i p : Degree G) :
    mourn (gesture i) (gesture p) (lag R x y)= if i.paint=p.paint then
      (slot checkout (List.ofFn p.layout) (slot checkin (List.ofFn i.layout) (fourier R.side i.a p.a)) ((x+i.point)-(y+p.point))).re else 0:=by
  rw [moves _ _ _ (bright_gesture _)]
  change jumps p.degree p.layout (fun z => jumps i.degree i.layout (fun w=> lag R x y (w,i.a,i.paint) (z,p.a,p.paint)) i.point) p.point=_
  simp only [lag_spectral]; split_ifs with h
  · simp_rw [paid_step]; exact paid_neg ..
  have he (k) (t : Fin k → Axis) (z : Cover) : jumps k t (fun _=>(0:ℝ)) z=(0:ℝ):=congr_fun (jumps_zero k t) z
  conv_lhs=> arg 3; ext; rw [he]
  exact he _ _ _

-- leading `decree` comparison with Maxwell leg conventions.
def actsOn (j : ℕ) (L : Module.Dual ℝ (Horizon G)): Probe G j:= L ∘ₗ sweep j ∘ₗ gaugeJet
lemma actual_leg (p : Degree G): actsOn p.degree (gesture p)=(p.degree.factorial:ℝ) • constrain (G:=G) (fromF G (basis ∘ p.layout) p.paint p.a.val.1 p.a.val.2):=by
  ext1 u
  let x:=gaugeJet u
  change gesture p (sweep _ x)= (p.degree.factorial:ℝ) * u.val _ _ _ _
  rw [gesture_hits,show sweep _ x=inspect x from rfl, Beamer.inspected,CellsInt.test_top, ← match_leg u]; rfl
lemma lowers (L : Module.Dual ℝ (Horizon G)) (c : Reading G j r→ℝ)
    (h : ∀ f : Horizon G,shutter f→ L f=∑ i,c i * gesture (mood i) f): actsOn j L=∑ i, c i • actsOn j (gesture (mood i)):=by
  ext1 p; rw [actsOn,LinearMap.comp_apply,LinearMap.sum_apply]; exact h _ (shutters _)

private lemma rode (t : Fin j→Axis) {z : E4} {f : E4 → ℝ} (h : ContDiffAt ℝ ∞ f z): ride (List.ofFn t) f z=(j.factorial:ℝ)*Tensor.coeff f j z (basis ∘ t):=by
  induction j generalizing f with
  | zero=>simp [ride,Tensor.coeff]
  | succ j ih=>
    let i:= t 0; let s:=Fin.tail t; have he:= h.of_le (show (↑(j+1:ℕ):ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    rw [List.ofFn_succ,ride,show basis ∘ t= Fin.cons (basis i) (basis ∘ s) by funext p; cases p using Fin.cases <;> rfl, Tensor.coeff_apply_cons he]
    change ride (List.ofFn s) (grad i f) z = _; rw [ih s (grad_smooth _ h (by simp))]; simp [grad,Nat.factorial_succ]; field_simp
private lemma curl_smooth (a b : PA) (z : E4) (h : z∈away) : ContDiffAt ℝ ∞ (legendary a b) z:=Maxwell.Bare.curl_diff h _ _ _ _

lemma matched_decree (p q : Degree G) {z : E4} (h : z∈away) :
    legKernel (actsOn p.degree (gesture p)) (actsOn q.degree (gesture q)) z=
    if p.paint=q.paint then decree (List.ofFn p.layout) (List.ofFn q.layout) p.a q.a z else 0 :=by
  change pairing h (actsOn _ _) (actsOn _ _) = _; rw [actual_leg,actual_leg, map_smul (pairing (G:=G) h (j:=p.degree) (l:=q.degree)),LinearMap.smul_apply,map_smul, raw_mixed _ _ _ _ _ _ _ _ h]; simp only [smul_eq_mul]; split_ifs with H; swap; simp
  unfold decree; let f:= legendary p.a q.a; let X x:= Tensor.coeff f p.degree x (basis ∘ p.layout); let c:ℝ:= p.degree.factorial
  have ht x (hx:x∈away): ContDiffAt ℝ ∞ X x:= (ContinuousMultilinearMap.apply ℝ _ ℝ (basis ∘ p.layout)).contDiff.contDiffAt.comp x (Tensor.coeff_smooth (curl_smooth p.a q.a x hx) _)
  have he : ride (List.ofFn p.layout) f =ᶠ[𝓝 z] c • X := by filter_upwards [Maxwell.open_away.mem_nhds h] with x hx; exact rode p.layout (curl_smooth p.a q.a x hx)
  change _=_*ride _ (ride _ f) z; rw [(ride_germ _ he).eq_of_nhds, rode q.layout (f:=c • X) ((ht z h).const_smul c), Tensor.coeff_smul c ((ht z h).of_le (WithTop.coe_le_coe.mpr le_top))]; dsimp only [c,X,f,legendary]; simp only [smul_apply,smul_eq_mul,List.length_ofFn]; ring


theorem journey (p q : Degree G) : ∃ C:ℝ,0<C∧∀ (R:Period) (x y : Cover),
    let z:= rcast (x+p.point-(y+q.point)); 1≤‖z‖→
    ‖mourn (gesture p) (gesture q) (lag R x y)- legKernel (actsOn p.degree (gesture p)) (actsOn q.degree (gesture q)) z‖ ≤
    C*((‖z‖^(5+p.degree+q.degree))⁻¹+(1+‖z‖)/(R.side.val:ℝ)):=by
  obtain ⟨C,hC,H⟩:=Episode.per_cost 1 one_pos 4 le_rfl (List.ofFn p.layout) (List.ofFn q.layout) p.a q.a
  refine ⟨C,hC,?_⟩; intro R x y z hz
  have hm : z≠0 := norm_pos_iff.mp (zero_lt_one.trans_le hz)
  rw [matched_mourn, matched_decree _ _ hm]; split_ifs with he
  · have ht:= H (.top 4) R.side (x+p.point-(y+q.point)) hz; rw [List.length_ofFn, List.length_ofFn] at ht
    rw [from_episode]; have hh (x : ℂ) (y : ℝ) : ‖x.re-y‖ ≤ ‖x-y‖ := by simpa using Complex.abs_re_le_norm (x-(y:ℂ))
    exact le_trans (hh _ _) ht
  rw [sub_self,norm_zero]; positivity
end YM.XSpace.Cross
