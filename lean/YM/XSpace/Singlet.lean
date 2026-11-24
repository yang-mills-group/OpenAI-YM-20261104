import YM.XSpace.Orbit

/-!
# A nontrivial stabilizer ambiguity in color cannot acquire *singlet* tangent hits

Tangent lemma, exploiting simplicity. Real-Euclidean, even determinant -1
allowed. Compact group here still the gauge group, not orthogonal output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sample
open Function Set Filter MeasureTheory Maxwell Maxwell.Free
open scoped BigOperators Topology Classical RealInnerProductSpace ContDiff
variable {G : Gauge}

def Ad (u:G.El) : Motor G:=(G.adjoint u).toContinuousLinearMap
lemma Ad_mul (u v : G.El): Ad (u*v)=Ad u * Ad v :=by ext1 x; exact G.adjoint_mul ..
lemma Ad_one : Ad (1:G.El)=1:= by ext1 x; exact G.adjoint_one ..
lemma Ad_inv (u:G.El):Ad u * Ad (u⁻¹)=1:=by rw [← Ad_mul,mul_inv_cancel, Ad_one]
lemma Ad_lin (u:G.El): Rot (Ad u):= G.norm_adjoint u
lemma Ad_cont : Continuous (Ad (G:=G)):= by
  suffices hh: Continuous fun u:G.El=> plank (Ad u) by
    have h:= pump_cont.comp hh; simpa only [Function.comp_def,able] using h
  let p:= fun u:G.El=> fun i:G.ColorIndex×G.ColorIndex => plank (Ad u) i
  have hp: Continuous p:= continuous_pi fun i=> (EuclideanSpace.proj i.1 : G.Color→L[ℝ] ℝ).continuous.comp (adj_cont (unitColor G i.2))
  exact (PiLp.continuous_toLp _ _).comp hp

lemma preserves_inner (M : Motor G) (h : Rot M) (x y:G.Color): ⟪M x,M y⟫=⟪x,y⟫:= by let Q : G.Color →ₗᵢ[ℝ] G.Color:=⟨M,h⟩; exact Q.inner_map_map ..

-- sign order chosen to use prob Haar's right invariance

def back (u:G.El): Motor G →L[ℝ] Motor G:= LinearMap.toContinuousLinearMap
  { toFun M:= Ad u⁻¹*M*Ad u
    map_add' M N:=by simp [mul_add,add_mul]
    map_smul' c X:=by ext1 x; change Ad u⁻¹ (c • X (Ad u x))=c • _; rw [map_smul]; rfl }
lemma back_at (u:G.El) (F:Motor G): back u F= Ad u⁻¹ * F * Ad u:= rfl
lemma back_cont (F:Motor G) : Continuous fun u:G.El=> back u F:= ((Ad_cont.comp continuous_inv).mul continuous_const).mul Ad_cont
lemma backs (u:G.El): back u (1:Motor G)=1:=by rw [back_at,mul_one,←Ad_mul,inv_mul_cancel,Ad_one]
lemma back_app (u v:G.El) (F:Motor G): back u (back v F)=back (v*u) F:=by simp only [back_at,Ad_mul,mul_inv_rev,mul_assoc]
lemma back_int (F:Motor G): Integrable (fun u:G.El=> back u F) G.probHaar:= (back_cont F).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
def Avg (F:Motor G):Motor G:= ∫ u:G.El, back u F ∂G.probHaar
lemma pull_avg (F:Motor G) (u:G.El): back u (Avg F)=Avg F:=by unfold Avg; rw [← (back u).integral_comp_comm (back_int F)]; simp_rw [back_app]; exact integral_mul_right_eq_self (μ:=G.probHaar) (fun v=> back v F) u
lemma braid (F:Motor G) (u:G.El) : Commute (Avg F) (Ad u):= by unfold Commute SemiconjBy; nth_rw 2 [← pull_avg F u]; rw [back_at,←mul_assoc,← mul_assoc, Ad_inv,one_mul]

def OrthoDev (F : Motor G): Prop:= ∀ x:G.Color,⟪x,F x⟫=0
lemma OrthoDev.backed {F:Motor G} (H:OrthoDev F) (u:G.El): OrthoDev (back u F):= by
  intro x; rw [← preserves_inner (Ad u) (Ad_lin u),← H (Ad u x)]; apply congr_arg; change (Ad u * back u F) x = _; rw [back_at, ←mul_assoc, ←mul_assoc, Ad_inv,one_mul]; rfl
lemma OrthoDev.avg {F:Motor G} (H:OrthoDev F): OrthoDev (Avg F):=by
  intro x; let L := innerSL ℝ x ∘L ContinuousLinearMap.apply ℝ G.Color x; change L (Avg F)=0; unfold Avg; rw [← L.integral_comp_comm (back_int F)]; simp_rw [show ∀ u,L (back u F)=0 from fun u=> H.backed u x]; exact integral_zero ..
lemma no_average (h : G.Simple) {F:Motor G} (H:OrthoDev F): Avg F=0:=by
  let Z := Avg F
  let B : G.Color →ₗ[ℝ] G.Color→ₗ[ℝ] ℝ:= innerₗ G.Color ∘ₗ Z.toLinearMap
  have hv (x y:G.Color): B x y= ⟪Z x,y⟫:=rfl
  obtain ⟨c,hc⟩:=invariant_two h B (fun u x y=> by
    rw [hv,hv,show Z (G.adjoint u x)= Ad u (Z x) from congr_arg (fun p:Motor G=> p x) (braid F u)]; exact preserves_inner _ (Ad_lin u) ..)
  have hh: c=0:=by
    haveI:= h.nontrivial_color; obtain ⟨x,hx⟩ := exists_ne (0:G.Color); refine (mul_eq_zero.mp (((hc x x).symm.trans (hv x x)).trans ((real_inner_comm x _).trans (H.avg x)))).resolve_right (by simpa using hx)
  ext1 x; change Z x=0; apply inner_self_eq_zero (𝕜:=ℝ) |>.mp; rw [← hv x, hc,hh,zero_mul]

abbrev play (p : WickPol G) (T:TaylorTower G):= fun M:Motor G=> probe (motor M T) p
abbrev differ (p: WickPol G) (T:TaylorTower G):= fderiv ℝ (play p T) 1
lemma differ_hit (p:WickPol G) (T:TaylorTower G): HasFDerivAt (play p T) (differ p T) 1 := ((travel_smooth ..).differentiable (by simp) _).hasFDerivAt

def Singlet (g:TaylorTower G →ℂ):Prop:= ∀ (T) (u:G.El),g (motor (Ad u) T)=g T
lemma sings {p:WickPol G} {d:ℕ} (h : p∈shellSector G d): Singlet fun T:TaylorTower G=> probe T p:=by
  intro T u; have hh: motor (Ad u) T=Maxwell.Free.shade u T:=rfl
  change probe _ p=probe T p; rw [hh, ← pigment_action,(sector.mp h).2 u]

lemma differ_ad (p:WickPol G) (H:Singlet (fun T:TaylorTower G=>probe T p)) (T:TaylorTower G) (u:G.El) (F:Motor G):
    differ p T (back u F)=differ p (motor (Ad u) T) F:=by
  have h:= (show HasFDerivAt (play p T) (differ p T) (back u 1) from backs u |>.symm ▸ differ_hit p T).comp 1 (back u).hasFDerivAt
  have he : play p T ∘ (back u) = play p (motor (Ad u) T):= by funext M; unfold play; rw [Function.comp_apply,back_at,motor_mul,motor_mul]; exact H _ (u⁻¹)
  rw [he] at h; exact congr_arg (fun z:Motor G→L[ℝ]ℂ=>z F) (h.unique (differ_hit ..))
lemma stops (h:G.Simple) {p : WickPol G} {d :ℕ} (hp:p∈shellSector G d) (F:Motor G)
    (he: OrthoDev F) (H : Singlet (fun T=> differ p T F)) (T : TaylorTower G) : differ p T F=0:=by
  have hi: (differ p T) (Avg F)=differ p T F:=by
    unfold Avg; rw [← (differ p T).integral_comp_comm (back_int F)]; simp_rw [differ_ad p (sings hp) T _ F,show ∀ u:G.El,differ p (motor (Ad u) T) F=differ p T F from H T]; simp
  rw [← hi,no_average h he,map_zero]
end YM.XSpace.Sample
