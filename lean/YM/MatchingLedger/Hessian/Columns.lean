import YM.MatchingLedger.Hessian.Carry

/-!
# Turns of one physical Hess wire
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Spring
open Function Filter Lattice Wilson RG Exterior Precision Work.F03 Pert Pert.Kinetic
open AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical ContDiff InnerProductSpace Finset
variable {n : Side} {G : Gauge} (c : G.Color) (s : Signed)

private def bend := ((pullDir (G:=G) s (0:Site n)).toLinearMap).comp (surf c)
private def pin (e:Edge (Site n)) : Floor n→ₗ[ℝ]G.Color:= (LinearMap.proj e).comp (bend c s)
-- explicit row instead of abstract H to see separation

def flute (x:Site n)(i j:Axis) : Floor n→ₗ[ℝ]G.Color:=
    pin c s (x+step i,j) - pin c s (x,j) - (pin c s (x+step j,i) - pin c s (x,i))

def curl (f:Face (Per n)):= flute c s f.1 f.2.val.1 f.2.val.2
variable (hn:4≤ n.val)
include hn
lemma curl_line (f:Face (Per n))(v:Floor n) : faceCurl f (Bid.pulled (lift1 (surf c v)) s)= curl c s f v:= by
  rw [← converts_dir s hn]; rcases f with ⟨x,⟨⟨i,j⟩,h⟩⟩; rw [faceCurl,← Exterior.fundamental, Square.cochain_square, back_wave]; rfl
omit hn

-- sendEdge budget due to base shift at flip; adapt Push.RelayDifference.Rolling
lemma between (i : Edge (Site n)) (x:Site n) : separation (sendEdge s 0 i).1 (affine s 0 x) ≤ separation i.1 x + 1 := by
    have hr : separation (affine s 0 i.1) (affine s 0 x) = separation i.1 x := spin_separation s _ _ _
    unfold sendEdge _root_.YM.Lattice.Step.used
    split
    · dsimp only; apply (separation_triangle _ (affine s 0 i.1) _).trans
      let a := ((posDir i.2).rotate s).dir
      rw [hr,separation,show affine s 0 i.1 - step a - affine s 0 i.1 = -step a by abel,pdist_neg]
      rw [add_comm]; exact Nat.add_le_add_left (pdist_step a) _
    · dsimp; exact le_trans hr.le (Nat.le_succ _)

private lemma bend_pin (i : Edge (Site n))(v:Floor n) : pin c s i v= StressFlux.sign s i.2 • surf c v (sendEdge s 0 i):= rfl
private lemma bend_ne (x y:Site n)(i:Axis) : pin c s (x,i) (1:Floor n)= pin c s (y,i) 1:= by rw [bend_pin,bend_pin, surf_apply c _ (sendEdge s 0 _).1 (sendEdge s 0 _).2, surf_apply c _ (sendEdge s 0 _).1 (sendEdge s 0 _).2, send_idx,send_idx]; rfl
lemma curl_plain (f : Face (Per n)) : curl c s f (1:Floor n)=0:= by unfold curl flute; simp only [LinearMap.sub_apply]; rw [bend_ne c s _ f.1 f.2.val.2,bend_ne c s (f.1+step f.2.val.2) f.1 f.2.val.1]; simp -- remove j arg

lemma curl_port (f : Face (Per n)) : Function.support (fun i=> ‖fieldRow (curl c s f) i‖) ⊆ ↑(halo 2 {affine s 0 f.1}):= by
  rintro u hu; contrapose hu; apply notMem_support.mpr
  let U:=affine s 0 f.1
  have hh: 2< separation u U:= by rw [separation_comm]; exact lt_of_not_ge (fun h=> hu (near_root.mpr h))
  have hz (x : Site n) (hx : separation f.1 x ≤ 1) (i : Axis) : pin c s (x,i) (spot u)=0:= by
    have h1 : (sendEdge s 0 (x,i)).1 ≠ u := by intro h; apply hh.not_ge; rw [← h]; exact (between s (x,i) f.1).trans (Nat.add_le_add_right ((separation_comm ..).trans_le hx) 1)
    rw [bend_pin,surf_spot, Pi.single_eq_of_ne (show _ from fun he: sendEdge s 0 (x,i)=(u,0)=> h1 (he ▸ rfl)),smul_zero]
  simp_rw [fieldRow,comp_apply,curl,flute, LinearMap.sub_apply]; rw [hz _ (Work.E01.sep_step_le ..), hz _ (by simp), hz _ (Work.E01.sep_step_le ..), hz _ (by simp)]; simp

variable {hc : ‖c‖=1}
include hc
private lemma pin_bound (u : Site n)(i:Edge (Site n)) : ‖pin c s i (spot u)‖ ≤ 1:= by rw [bend_pin, norm_smul]; have he:= surf_spot_norm c hc u (sendEdge s 0 i); unfold StressFlux.sign; split <;> simpa using he
lemma curl_bound (u:Site n)(f : Face (Per n)): ‖fieldRow (curl c s f) u‖ ≤ 4:= by
    let Q:=spot u; let i:=f.2.val.1; let j:=f.2.val.2; let x:= f.1
    simp only [fieldRow,comp_apply,curl,flute,LinearMap.sub_apply];
    have h (a b:Axis): ‖pin c s (x+step a,b) Q - pin c s (x,b) Q‖ ≤ 1+1:= (norm_sub_le ..).trans (add_le_add (pin_bound (hc:=hc) c s ..) (pin_bound (hc:=hc) c s ..))
    exact (norm_sub_le ..).trans (le_trans (add_le_add (h i j) (h j i)) (by norm_num))

def curlPay := 4 * (2+2+1)^4 * Real.exp 2
lemma curl_felt {r:ℝ} (he:r≤1)(f:Face (Per n)) : felt r (affine s 0 f.1) (fieldRow (curl c s f)) ≤ curlPay:= by
  apply (funded (affine s 0 f.1) 2 he (by norm_num : (0:ℝ)≤4) (curl_port ..) (fun i=>curl_bound (hc:=hc) c s i f)).trans_eq; simp [curlPay]
omit hc c in
lemma stride (w : Slot)(x:Site n) : separation (affine s 0 (slotFace w x).1) (affine s 0 x)≤ w.length:= by
  rw [spin_separation]; apply AnalyticBridge.VerifiedReset.slot_length w x (AnalyticBridge.VerifiedReset.offset_inside w x)
omit hc in
lemma curlPay_nn : 0≤ curlPay:= by unfold curlPay; positivity
lemma token_felt {r:ℝ} (hr:0≤r)(he:r≤1) (x:Site n) (w:Slot) : felt r (affine s 0 x) (fieldRow (curl c s (slotFace w x)))≤ curlPay*Real.exp (r*w.length):=
  (tilt hr (affine s 0 (slotFace w x).1) (affine s 0 x) _).trans (mul_le_mul (curl_felt (hc:=hc) c s he _) (Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast stride s w x) hr)) (beam_pos ..).le (by unfold curlPay; positivity)) -- arg implicit
end YM.MatchingLedger.Spring
