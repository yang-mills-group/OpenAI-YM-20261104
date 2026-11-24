import YM.FrontierTrace.Shear.Fields
import YM.Trace2.HeatGrowth

/-! Isotropic angular channel at the *actual Final*, with offdiag tilt. Orth covariance
of both ends; moving frames need only be H covariant (ExactTurns provided by fixed Final).
No contact terms: all t>0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrontierTrace
open Function Filter Set Analysis Trace MeasureTheory Table Climb
open Next.UVStress Work.A01
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace

variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} (F:Spec.Final C f S)
    {r s:ℝ}
local notation "μ0" => timeAxis
/-- Spectator at 0, stress-probe direction unconstrained (O_4 transports to radial). -/
def atShape (z:E4):Points 2:= Points.cons z (0:Points 1)
lemma atRoom {z:E4} (hz:z≠0) : atShape z∈ conf 2:= by
    rintro i j he; fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hz he)
    · exact False.elim (hz he.symm)
    · rfl
lemma atShape_cov (s:Ortho) (z:E4): Points.move s (atShape z) = atShape (Ortho.move s z) := by
    rw [atShape,move_cons,show Points.move s (0:Points 1)=0 from PiLp.ext fun _=> map_zero (Ortho.motion s)]; rfl
lemma onShape (U:E4)(r:ℝ): r • atShape U = atShape (r • U):= (map_smul (headDir 1) r U).symm

def slice (s:ℝ) : E4:= s • basis timeAxis
lemma slice_nonzero (hs:0<s): slice s≠0:= smul_ne_zero hs.ne' (norm_ne_zero_iff.mp (by rw [basis_norm]; exact one_ne_zero))

lemma custom_move {l m:ℕ} (u:S.Field l) (v:S.Field m) (s:Ortho) {z:Points 2} (hz:z∈conf 2) :
    custom (Points.move s z) (F.sector.turns.act l s u) (F.sector.turns.act m s v) = custom z u v := by
   let t:= Fin.cons (α:=fun _:Fin 2=> S.Tag) ⟨l,u⟩ (fun _=> ⟨m,v⟩)
   have h := F.phase.transport.motion 2 t z hz s
   rw [show F.sector.turns.label s ∘ t = Fin.cons (α:=fun _:Fin 2=>S.Tag) ⟨l,F.sector.turns.act l s u⟩
     (fun _=> ⟨m,F.sector.turns.act m s v⟩) from funext (Fin.cases rfl (fun _=>rfl))] at h
   exact h

lemma unit_aim (ℓ:E4)(hℓ:‖ℓ‖=1):∃ U:Ortho, Ortho.move U (basis μ0)=ℓ := by
   obtain ⟨U,hU⟩:= Trace.rotation_exists ℓ
   exact ⟨U,by simpa only [hℓ,one_smul] using hU⟩

lemma aim_ne (ℓ:E4)(hℓ:‖ℓ‖=1)(s:ℝ)(hs:0<s): s • ℓ≠0:=
   smul_ne_zero hs.ne' (norm_ne_zero_iff.mp (hℓ.symm ▸ one_ne_zero))

/- `m` factor is the insertion normalization, not chosen to fit.
Uncentered exact stress slot, use centered scalar A at the other.
-/
variable (A : S.Field 4) (m : ℝ)
def current (i j:Axis)(z:E4):ℂ:= custom (atShape z) (m • F.sector.energy i j) A
def currentL (s:ℝ):ℂ:= YM.FrontierTrace.current F A m μ0 μ0 (slice s)
def currentS (s:ℝ):ℂ:= YM.FrontierTrace.current F A m 0 0 (slice s)
def currentB (s:ℝ):ℂ:= currentL F A m s - currentS F A m s
local notation "J" => F.sector.energy
local notation "X" => F.sector.turns
local notation "T" => YM.FrontierTrace.current F A m
variable (hA : ∀ g:Ortho, F.sector.turns.act 4 g A=A)

include hA
lemma custom_aim (ℓ:E4)(hℓ:‖ℓ‖=1)(s:ℝ)(hs:0<s): custom (atShape (s • ℓ)) A A = custom (atShape (slice s)) A A:= by
   obtain ⟨U,hU⟩:= unit_aim ℓ hℓ
   have hz: Points.move U (atShape (slice s))=atShape (s • ℓ):= by
      rw [atShape_cov]; apply congr_arg; exact (map_smul (Ortho.motion U) s _).trans (congr_arg (s • ·) hU)
   rw [← hz]; exact (by simpa only [hA] using custom_move F A A U (atRoom (slice_nonzero hs)))

lemma current_cov (z:E4)(hz:z≠0)(g:Ortho)(i j:Axis): T i j (Ortho.move g z) = ∑ k:Axis,∑ l:Axis,(g.val i k *g.val j l) • T k l z:= by
   let q:=Ortho.move g z

   have he' : q≠0:= by intro h; exact hz ((Ortho.move_injective g) (h.trans ((Ortho.motion g).map_zero.symm)))
   have hq := (custom_move F (m • J i j) A g⁻¹ (atRoom (z:=q) he')).symm
   rw [atShape_cov, show Ortho.move g⁻¹ q=z from Ortho.inv_move g z,hA g⁻¹] at hq
   obtain ⟨L,hL⟩:= Trace.custom_linear (e:=4) (atShape z) A
   unfold YM.FrontierTrace.current
   rw [hq, RCLike.real_smul_eq_coe_smul (K:=ℂ) m,
     map_smul,F.phase.transport.spin]
   simp_rw [hL,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,map_sum]
   rw [Finset.smul_sum]; apply Finset.sum_congr rfl
   intro k _; rw [Finset.smul_sum]; apply Finset.sum_congr rfl
   intro l _; rw [Maxwell.Free.inv_entry g,Maxwell.Free.inv_entry,map_smul]; exact smul_comm ..

lemma current_signed (z:E4)(hz:z≠0)(s:Signed)(i j:Axis):
   T i j z = (eps s i * eps s j) • T (s.perm i) (s.perm j) (Ortho.move s.ortho z):= by
   have hk : RawTensor F.room.kernel.spin J:= fun s i j=>by rw [←F.phase.transport.spots.signed]; exact F.phase.transport.spin ..
   have ho := (custom_move F (m • J i j) A s.ortho (atRoom hz)).symm
   unfold YM.FrontierTrace.current
   rw [ho,hA,atShape_cov, RCLike.real_smul_eq_coe_smul (K:=ℂ) m, map_smul, F.phase.transport.spots.signed, tensor_column hk]
   obtain ⟨L,hL⟩:= Trace.custom_linear (e:=4) (atShape (Ortho.move s.ortho z)) A
   simp_rw [hL,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul]
   exact smul_comm ..

omit hA in
lemma slice_flip (s:Signed)(h:s.perm μ0=μ0)(hs:eps s μ0=1)(t:ℝ): Ortho.move s.ortho (slice t)=slice t:=by
   unfold slice
   rw [← Ortho.motion_at]; rw [map_smul]; congr 1; rw [Ortho.motion_at,move_basis,hs,h,one_smul]

private lemma vanish1 (t:ℝ)(ht:0<t)(i j:Axis)(h:i≠μ0)(he:i≠j): T i j (slice t)=0:=by
   let s:=Signed.mirror i; have hk:= current_signed F A m hA _ (slice_nonzero ht) s i j
   have hm : eps s μ0 = 1 := by dsimp [s]; rw [UVNext.FreeStress.eps_mirror_bit]; simp [UVNext.FreeStress.bit,Ne.symm h]
   rw [slice_flip s rfl hm] at hk
   have hi:eps s i = -1:=by dsimp [s]; rw [UVNext.FreeStress.eps_mirror_bit]; simp [UVNext.FreeStress.bit]
   have hj:eps s j = 1:=by dsimp [s]; rw [UVNext.FreeStress.eps_mirror_bit]; simp [UVNext.FreeStress.bit,Ne.symm he]
   rw [hi,hj,mul_one,neg_one_smul] at hk
   change T i j (slice t)= -T i j _ at hk
   have ht := eq_neg_iff_add_eq_zero.mp hk; rw [← two_mul] at ht
   exact (mul_eq_zero.mp ht).resolve_left two_ne_zero
lemma vanish_slice (s:ℝ)(hs:0<s)(i j:Axis)(he:i≠j): T i j (slice s)=0 := by
   by_cases h:i=μ0
   · rw [YM.FrontierTrace.current,F.phase.transport.conserved.symmetric]; exact vanish1 F A m hA s hs j i (h ▸ he.symm) he.symm
   exact vanish1 F A m hA s hs i j h he
lemma transverse_slice (s:ℝ)(hs:0<s)(i:Axis)(hi:i≠μ0): T i i (slice s)=currentS F A m s:= by
   let t:= UVNext.FreeStress.round (Equiv.swap i 0)
   have ht : t.perm i=0 := Equiv.swap_apply_left ..
   have h := current_signed F A m hA (slice s) (slice_nonzero hs) t i i
   rw [slice_flip t ?_ (UVNext.FreeStress.eps_round (Equiv.swap i 0) μ0) s,ht, eps_self,one_smul] at h -- check namespace args
   · exact h
   exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (by decide)

lemma inline (s:ℝ)(hs:0<s)(i j:Axis) :
    T i j (slice s) = (if i=j then currentS F A m s else 0)+
      if j=μ0 ∧ i=μ0 then currentB F A m s else 0:=by
   by_cases h:i=j
   · subst j; by_cases h:i=μ0
     · subst i; unfold currentB currentS currentL; simp
     simp [h, transverse_slice F A m hA s hs i h]
   have he: ¬ (j=μ0∧i=μ0):= fun Q=> h (Q.2.trans Q.1.symm)
   rw [vanish_slice F A m hA s hs i j h,if_neg h,if_neg he,add_zero]

set_option maxHeartbeats 600000 in
theorem slope_angle (ℓ:E4)(hl:‖ℓ‖=1)(s:ℝ)(hs:0<s)(i j:Axis) :
    T i j (s • ℓ) = (if i=j then currentS F A m s else 0) + (ℓ i * ℓ j) • currentB F A m s:=by
  obtain ⟨U,hU⟩:= unit_aim ℓ hl
  have he (k:Axis) : U.val k μ0=ℓ k := by rw [←hU]; exact (M4.move_basis ..).symm
  have hv : Ortho.move U (slice s)=s • ℓ:= (map_smul (Ortho.motion U) s _).trans (congr_arg _ hU)
  rw [←hv,current_cov F A m hA _ (slice_nonzero hs)]
  simp_rw [inline F A m hA s hs,smul_add,Finset.sum_add_distrib]
  congr 1
  · simp_rw [smul_ite,smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,←Finset.sum_smul]
    rw [show (∑ k:Axis,U.val i k * U.val j k) = if i=j then 1 else 0 from Maxwell.Free.col_dot U⁻¹ i j]
    split <;> simp
  rw [Finset.sum_eq_single μ0]
  · rw [Finset.sum_eq_single μ0]
    · rw [if_pos (And.intro rfl rfl),he,he]
    · simp +contextual
    · simp
  · intro x _ hx; exact Finset.sum_eq_zero fun y _ => by rw [if_neg (fun h=> hx h.2),smul_zero]
  simp

end YM.FrontierTrace
