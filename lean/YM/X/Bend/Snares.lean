import YM.X.Bend.Morals
import YM.X.Jet.Inverter
/-!
# Dossier ∑ coupled-profile products. Exact real and parity. seven entries for connected.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Maxwell Set Function MeasureTheory Lattice Wilson Next.Rank Labels Pert.Position
open Maxwell.Free Filter Metric Chir Sage Tri Ribbon Extra.FD
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {d k m n:ℕ} {q:ℕ+} {V I:Type*} {r R:ℝ}
local notation "K"=>(atTop:Filter ℕ)
local notation "T"=> Fin 3
local notation "W"=>Bank F 6
local notation "M"=>Pert.Position.Section F 6
local notation "γ"=> par F 6
variable (hr:4096≤ r) (B:Bare.Shop F) (A:Bank F 6)
def cell (i:T) : Fin 1↪ Fin 3 := ⟨fun _=>i, fun x y _=>Subsingleton.elim ..⟩
def couplet (i j:T)(h:i≠j:=by decide) : Fin 2↪Fin 3:= ⟨![i,j],fun x y he=> by fin_cases x<;> fin_cases y<;> first| rfl|exact (h he).elim| exact (h he.symm).elim⟩
set_option quotPrecheck false
local notation "U"=>MU F (by decide:4≤6)
local notation "b"=> BB F (Nat.le_refl 6)
abbrev clerk0 (hr:4096≤ r): M:= ⟨3,beaconLabels F (Nat.le_refl 6), mainT r hr⟩
abbrev clerkz :M:= ⟨1,(fun _=>b), Eyes r (cell 0) hr⟩
abbrev clerkx : M:=⟨1,fun _=>U, Eyes r (cell 1) hr⟩
abbrev clerky : M:=⟨1,fun _=>U, Eyes r (cell 2) hr⟩
abbrev zx :M:=⟨2,![b,U],Eyes r (couplet 0 1) hr⟩
abbrev zy :M:=⟨2,![b,U],Eyes r (couplet 0 2) hr⟩
abbrev xy :M:=⟨2,(fun _=>U),Eyes r (couplet 1 2) hr⟩
abbrev Tea:=Fin 7
def menu (F:Frames G)(hr:4096≤ r): Fin 7→Pert.Position.Section F 6:= ![clerk0 hr,clerkz hr,clerkx hr,clerky hr,zx hr,zy hr,xy hr]
-- moment sign under `par` distinguishes entire formal stream
abbrev billSign : Fin 7→ℝ:= ![-1,-1,1,1,-1,-1,1]
abbrev poseF (hr:4096≤ r)(i:Tea): Bank F 6→ₗ[ℝ] ℂ:= lookie F (menu F hr i)
lemma realtE (f:Fin m↪ Fin 3): RealT (Eyes r f hr):= fun x=> by unfold moral; rw [stencil_eye]; simp
lemma mood_BB : (∀ i, (Model F).conj (hierarchy F).spin 6 (beaconLabels F (Nat.le_refl 6) i)= beaconLabels F (Nat.le_refl 6) i):= fun i=> by rw [mounts]; fin_cases i<;> first|exact bar_beta _|exact bar_mu _
set_option maxHeartbeats 550000 in
lemma moral_menu (i:Fin 7)(h:House A): moral (poseF hr i A):= by
     apply h; all_goals first| (fin_cases i<;> exact realtE hr _)|(intro j; fin_cases i <;> first|exact bar_beta _ | exact bar_mu _ | exact mood_BB j| (fin_cases j<;> first|exact bar_beta _|exact bar_mu _)) -- try
section w
variable {u:Fin n→E F 6}(t:Test n)
lemma bill_even (h:∀i,γ (u i)=u i): (pulls γ A) n t u=A n t u:= congr_arg _ (show γ ∘ u=u from funext h)
lemma bill_odd (i:Fin n)(h:γ (u i)=-u i)(hp:∀j,j≠i→γ (u j)=u j):(pulls γ A) n t u= -A n t u:= by
   change A n t (γ ∘ u)=_; rw [show γ ∘ u= update u i (-u i) from ?_,MultilinearMap.map_update_neg,Function.update_eq_self]; funext j; by_cases hx:j=i <;> first|(subst j;rw [Function.update_self];exact h)|(rw [Function.update_of_ne hx]; exact hp j hx)
omit hr
end w
lemma signs_p0 (t:Test 3) : let v:=beaconLabels F (Nat.le_refl 6); (pulls γ A) 3 t v= -A 3 t v:= by
     intro v; unfold v; rw [mounts]; exact bill_odd A _ (i:=0) (signB _) (fun j hj=> by fin_cases j<;> first|exact False.elim (hj rfl)| exact signU _)
lemma signs_p1 (t:Test 1) : (pulls γ A) 1 t (fun _=>b)= -A 1 t (fun _=>b):= bill_odd A _ 0 (signB _) (fun i hi=>False.elim (hi (Subsingleton.elim ..)))
lemma signs_p2 (t:Test 2):(pulls γ A) 2 t ![b,U]= -A 2 t ![b,U]:= bill_odd A _ 0 (signB _) (fun i hi=> by fin_cases i<;> first|exact False.elim (hi rfl)| exact signU _)
lemma signs_u (t:Test m) : (pulls γ A) m t (fun _=>U)=A m t (fun _=>U):= bill_even A t (fun _=> signU _)
lemma dark (i: Fin 7) : poseF hr i (pulls γ A)= billSign i • poseF hr i A:= by
     let v:ℕ:=6; let p:Fin 7→W→ₗ[ℝ]ℂ:= poseF hr; let α:= p -- construct explicit equival
     fin_cases i
     · change _=(-1:ℝ) • poseF hr 0 A; rw [neg_one_smul]; exact signs_p0 A (mainT r hr)
     · change _=(-1:ℝ) • poseF hr 1 A; rw [neg_one_smul]; exact signs_p1 A (Eyes r (cell 0) hr)
     · change _=(1:ℝ) • poseF hr 2 A; rw [one_smul]; exact signs_u A (Eyes r (cell 1) hr)
     · change _=(1:ℝ) • poseF hr 3 A; rw [one_smul]; exact signs_u A (Eyes r (cell 2) hr)
     · change _=(-1:ℝ) • poseF hr 4 A; rw [neg_one_smul]; exact signs_p2 A (Eyes r (couplet 0 1) hr)
     · change _=(-1:ℝ) • poseF hr 5 A; rw [neg_one_smul]; exact signs_p2 A (Eyes r (couplet 0 2) hr)
     · change _=(1:ℝ) • poseF hr 6 A; rw [one_smul]; exact signs_u A (Eyes r (couplet 1 2) hr)
def Board7 (F:Frames G)(hr:4096≤ r):Bank F 6→ₗ[ℝ] (Tea→ℂ):= LinearMap.pi (poseF hr)
include B
lemma board_m (hq:1<q.val): Board7 F hr (pureBank F 6)=0:= by
    ext1 i; fin_cases i
    · exact white_call (Nat.le_refl 6) B (mainT r hr)
    · exact whiteB1 (Nat.le_refl 6) B (Eyes r (cell 0) hr)
    · exact white_u B hq (by decide: 4≤6) (Eyes r (cell 1) hr)
    · exact white_u B hq (by decide:4≤6) (Eyes r (cell 2) hr)
    · exact whiteBa (Nat.le_refl 6) B (Eyes r (couplet 0 1) hr)
    · exact whiteBa (Nat.le_refl 6) B (Eyes r (couplet 0 2) hr)
    · exact white_p B hq (by decide:4≤6) (Eyes r (couplet 1 2) hr)
end YM.PositionX.Bend
