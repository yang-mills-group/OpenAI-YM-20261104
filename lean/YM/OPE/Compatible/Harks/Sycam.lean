import YM.OPE.Compatible.Harks.Clean
/-!
# layers of paid small initial/correction directions
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {E F M:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] {r x b c t q:ℝ}
variable {a f:ℕ→ E}{g:ℕ→ F}{p:ℕ→ E→L[ℝ] E}
variable {d k:ℕ}{G:ℕ→Type}[∀ i,NormedAddCommGroup (G i)][∀ i,NormedSpace ℝ (G i)]
variable {μ:ℕ→ℝ}{T:Cuts d μ t x E G}
-- stationary matrix.Late representations. invert on higher grades using λ growth.
variable (R:E→L[ℝ] E)
def Ux (R:E→L[ℝ] E)(v:ℝ):E→L[ℝ] E:= R-v • 1
lemma shiftUx (u:ℝ)(a:E): Ux R u a= R a-u • a:=by rfl -- name
abbrev Ford (R:E→L[ℝ] E) (_:ℕ):=R
abbrev tale (R:E→L[ℝ] E)(b:E)(i:ℕ):= (R^i) b
lemma byway (P Q:E→L[ℝ] E)(v:E): (P*Q) v=P (Q v):=rfl
lemma TALE (v:E): Run (Ford R) (tale R v) 0:=fun i=>by simp only [Ford,tale, pow_succ',Pi.zero_apply,add_zero,byway]
variable {R}
lemma jumps_in (h:Grooved T R){k:ℕ}(hk:k≤d)(v:E)(hp:v∈T.flag k): Ux R q v∈T.flag k:= (T.flag _).sub_mem (h.leaves k hk v hp) ((T.flag _).smul_mem q hp)
lemma TapJump (h:Grooved T R){k:ℕ}(hk:k<d)(v:E)(hp:v∈T.flag k): T.Tap k (Ux R q v) = (μ k-q) • T.Tap k v:=by rw [shiftUx,map_sub,map_smul,h.tempo k hk v hp,sub_smul]
lemma TapDeep (h:Grooved T R) {k:ℕ}(hk:k<d)(v:E)(hp:v∈T.flag k)(i:ℕ):(Ux R q ^ i) v∈T.flag k ∧ T.Tap k ((Ux R q ^ i) v)= (μ k-q)^i • T.Tap k v:=by
    induction i with
    | zero=> simp [hp]
    | succ i ih=> rw [pow_succ',byway]; exact ⟨jumps_in h hk.le _ ih.1,by rw [TapJump h hk _ ih.1,ih.2,pow_succ',smul_smul]⟩
lemma not_eig (h:Grooved T R)(hk:k< d)(w:E)(n:ℕ)(hp:(Ux R (μ k)^n) w=0): w∈ T.flag k:=by
    have hx:∀ i:ℕ,i ≤ k→ w∈ T.flag i:=by
         intro i hi; induction i with | zero=> exact T.first w| succ i ih=> have hh:= ih (by omega); refine (T.next _ (by omega) _).mpr ⟨hh,?_⟩; apply (smul_eq_zero.mp _).resolve_left (pow_ne_zero n (sub_ne_zero.mpr (T.beats i k (by omega) hk).ne')); rw [← (TapDeep h (by omega) _ hh n).2,hp,map_zero]
    exact hx k le_rfl
variable [∀ i,CompleteSpace (G i)]
-- Need r frame slot
lemma exitE (h:Grooved T R)(hk:k< d)(hb:ShadeR T (k+1) r)(u:E)(hv:u∈T.flag (k+1))(hy: Ux R (μ k) u=0) :u=0:=by
    have hr:=T.tempo k hk; obtain ⟨b,Hb,H⟩:= even T hb.Fast hb.ex (k+1) (by omega) hb.brisk; let v:=tale R u; have hp:Hex r v (b*‖v 0‖):= H (Ford R) (fun _=>h) _ (TALE R u) hv; have hx:R u=(μ k) • u:= sub_eq_zero.mp hy
    have hg(i:ℕ): R (v i)=(μ k) • v i:=by
         unfold v tale; rw [← byway,Commute.self_pow R i|>.eq,byway,hx,map_smul]
    apply show v 0=0 from det (T.fast.trans hb.Fast.le) (hb.slow k (by omega)) _ hp; intro i; refine (TALE R u i).trans ?_; rw [show Ford _ _ _=R (v i) from rfl,hg]; rfl
lemma FinalJump (h:Grooved T R)(hk:k<d)(hb:ShadeR T (k+1) r)(i:ℕ)(v:E)(hv:v∈T.flag (k+1))(hp:(Ux R (μ k)^i) v=0):v=0:=by
    induction i generalizing v with
    | zero=> simpa using hp
    | succ i ih=> rw [pow_succ,byway] at hp; exact exitE h hk hb v hv (ih _ (jumps_in h (by omega) v hv) hp)
lemma kern (h:Grooved T R)(hk:k<d)(hb: ShadeR T (k+1) r)(i:ℕ)(v:E)(hp:(Ux R (μ k)^i) v=0): Ux R (μ k) v=0:=by
     have hr:= not_eig h hk v i hp; let B:=Ux R (μ k); let x:=B v; have hh:x∈ T.flag (k+1):=(T.next k hk _).mpr ⟨jumps_in h hk.le v hr,by unfold x B;rw [TapJump h hk _ hr,sub_self,zero_smul]⟩; refine FinalJump h hk hb i x hh ?_; change (B^i) (B v)=_; rw [← byway,← Commute.eq (Commute.self_pow B i),byway]; erw [hp,map_zero]
end YM.OPE.Hark
