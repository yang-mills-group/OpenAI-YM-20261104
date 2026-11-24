import YM.XSpace.Theme

/-!
# Gauge-translated jets, including polynomial gauge freedoms

Ward argument in contact estimates only needs on-shell gauge invariant ambiguities;
here is the exact kernel/image characterization that allows using grade-pure physical
labels to remove all polynomial divergences. Centers fixed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Scale
open Lattice Litter Maxwell Maxwell.Free Tensor Sail Further.FreeCovariance.KP Analysis Filter Function
open scoped Topology BigOperators ContDiff
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{G:Gauge}{d:ℕ}

def stream: (Cover→F)→ₗ[ℝ] Tape F:= LinearMap.pi fun x=> LinearMap.proj x.1 ∘ₗ teeth x.2
lemma notated (v:Cover→ G.Color): stream v=Chart2.grad v:=rfl
lemma stream_ap (p:Cover→F)(i:Axis)(x:Cover):stream p (x,i)= Δf i p x:=rfl
lemma stream_curl (p:Cover→F)(i j:Axis): crackle i j (stream p)=0:= sub_eq_zero.mpr (chosen i j p)
lemma river (p:Cover→F): press (stream p)=0:= fare.mpr fun i=> by simp_rw [job,stream_curl,map_zero,Finset.sum_const_zero]

def blow : Stamp (d+1) F →ₗ[ℝ] Vase d F:=LinearMap.pi fun i=> dip i
lemma blown (A:Stamp (d+1) F): release (blow A)=stream (feed 0 A):=by funext x; rcases x with ⟨x,i⟩; rw [stream_ap,feed_one,zero_add];rfl
lemma blower (A:Stamp (d+1) F): blow A∈motif d F:= by change press (release _)=0; rw [blown,river]
def pipes : Stamp (d+1) F →ₗ[ℝ] Tune d F:= blow.codRestrict _ blower
lemma quiet (A:Stamp (d+1+1) F): ink (pipes A)=0:=by
  apply Subtype.ext; change draw _=0; funext i j; change (pair i j (blow A)).val= 0; suffices h: pair i j (blow A)=0 by rw [h]; rfl
  apply once_hard (v:=half i+half j); rw [← sounds,blown,stream_curl,map_zero]

private def entered (A:Vase d F): Stamp (d+1) F:= (↑(d+1:ℕ):ℝ)⁻¹ • ∑ i:Axis, (⟨added (A i).val (compAxis i), added_sym (A i).val (compAxis i)⟩ : Stamp (d+1) F)
private lemma entry (A:Vase d F): motifValue (entered A)=fun x=> (↑(d+1:ℕ):ℝ)⁻¹ • ∑ i:Axis, x i • motifValue (A i) x:=by
  funext x; rw [motif_pop, entered,map_smul,map_sum]; exact congr_arg _ (Finset.sum_congr rfl fun i _=> added_diag (A i).val (compAxis i) x)
private lemma entered_back (A:Tune d F)(h:∀ i j,crackle i j (release A.val)=0) : A=pipes (entered A.val):=by
  let p:=entered A.val; let v (i:Axis):= motifValue (A.val i)
  have thread (i j:Axis)(x:E4): grad i (v j) x = grad j (v i) x:=by
    unfold v
    cases d with
    | zero=> rw [plane,plane]
    | succ d=> specialize h i j; rw [sounds,map_eq_zero_iff _ (once_hard _)] at h; rw [climbs,climbs]; exact congr_arg (fun q:Stamp d F=>motifValue q x) (sub_eq_zero.mp h)
  apply Subtype.ext; funext i; apply motif_inj; funext x
  let a:ℝ:=(d+1:ℕ); have ha: a≠0:=by unfold a; positivity
  change v i x = motifValue (dip i p) x; rw [← climbs, show motifValue p=a⁻¹ • (fun x : E4=>∑ i:Axis,x i • v i x) from entry _]; symm
  have he : DifferentiableAt ℝ (fun x:E4=>∑ i:Axis,x i • v i x) x:= DifferentiableAt.fun_sum fun i _=> (compAxis i).differentiableAt.smul ((diag_smooth (A.val i).val ∞).differentiable (by simp) _)
  rw [show grad i (a⁻¹ • (fun x : E4=>∑ i:Axis,x i • v i x)) x = a⁻¹ • (v i x + ∑ k:Axis,x k • grad i (v k) x) from ?_]
  · simp_rw [thread i]; rw [show ∑ k:Axis,x k • grad k (v i) x=_ from grad_euler _ (A.val i).property x]; change a⁻¹ • (v i x+ (↑d:ℝ) • v i x)=_
    rw [show v i x+ (↑d:ℝ) • v i x= a • v i x from ?_,inv_smul_smul₀ ha]; unfold a; rw [Nat.cast_add,Nat.cast_one,add_smul,one_smul,add_comm]
  let q:=fun x:E4=>∑ i:Axis,x i • v i x; change fderiv ℝ (a⁻¹ • q) _ _=_; rw [fderiv_const_smul he]; exact congr_arg (a⁻¹ • ·) (grad_self (fun i=> (A.val i).val) i x)
lemma start_empty (A:Tune 0 F): A=pipes (entered A.val):= entered_back A fun i j=> soundless _ i j
lemma inker (A:Tune (d+1) F)(h:ink A=0): A=pipes (entered A.val):=by
  apply entered_back; intro i j; rw [sounds]; apply (map_eq_zero_iff _ (once_hard _)).2; exact Subtype.ext (congr_arg (fun v:Solution F d=>v.val i j) h)

-- explicit color-compatible grade-preserving projections to read invariant ambiguities
def assay : (d:ℕ)→ Tune d G.Color →ₗ[ℝ] Tune d G.Color
| 0 =>0
| _+1=> roll ∘ₗ ink
lemma assayed (A:Tune d G.Color): ∃ p:Stamp (d+1) G.Color,A=assay d A+pipes p:=by
  cases d with
  | zero=> exact ⟨_, ((start_empty A).trans (zero_add _).symm)⟩
  | succ d=>
    let p:= A-assay (d+1) A; have he:ink p=0:=by rw [show p=A- roll (ink A) from rfl,map_sub (ink (F:=G.Color) (d:=d)),inks,sub_self]
    refine ⟨entered p.val,?_⟩; rw [← inker p he]; unfold p; abel

-- note that `Tune d` is genuine graded: no combination of violations across degrees.
-- synthesis over `Π i:Fin (D+1), Vase` gets K equations independently.
abbrev Folder (d:ℕ)(F:Type*)[NormedAddCommGroup F][NormedSpace ℝ F]:= (i:Fin (d+1))→ Vase i.val F
def castBlaze : Folder d F→ₗ[ℝ] Tape F:=∑ i:Fin (d+1),release ∘ₗ LinearMap.proj i

private lemma disk_void (n:ℕ)(A: Vase n F)(h:n<2): press (release A)=0:=by
  interval_cases n; exact origin A; exact start A
private lemma higher (n:ℕ)(A: Vase n F)(k:ℕ)(h:n<k+2)(i): grasp k (twig i (press (release A)))=0:=by
  by_cases H:n<2; rw [disk_void n _ H,map_zero,map_zero]; obtain ⟨d,rfl⟩:∃ d,n=d+1+1:= ⟨n-2,by omega⟩; rw [Scale.string,map_neg, flunked (d:=d) (n:=k) _ _ (by omega),neg_zero]
private lemma set_void (k:ℕ)(A:Vase (k+2) F)(i): twig i (press (release A))=0 ↔ grasp k (twig i (press (release A)))=0:=by rw [Scale.string,map_neg,poured,neg_eq_zero,neg_eq_zero,map_eq_zero_iff _ (once_hard _)]
theorem similar (A:Folder d F):press (castBlaze A)=0↔∀ i,A i∈motif i.val F:=by
  unfold castBlaze; rw [LinearMap.sum_apply,map_sum]; simp only [LinearMap.comp_apply,LinearMap.proj_apply]; constructor
  · intro h i; induction i using WellFoundedGT.induction with
    | _ i ih=>
      by_cases he:i.val<2; exact disk_void _ _ he
      change press (release (A i))=0; apply fare.mpr; intro j
      obtain ⟨k,hk⟩:∃ k,i.val=k+2:= ⟨i.val-2,by omega⟩
      have hw:∀ v:Vase i.val F,twig j (press (release v))=0 ↔ grasp k (twig j (press (release v)))=0:=by rw [hk]; exact fun v=>set_void k v j
      apply (hw _).2; have hz:=congr_arg (fun u:Tape F=>grasp k (twig j u)) h; change grasp _ (twig _ _) = _ at hz; rw [map_sum,map_sum,Finset.sum_eq_single i] at hz; exact hz.trans (by simp); swap; · simp
      intro i' _ H; cases lt_or_gt_of_ne H with
      | inl h=> exact higher _ _ _ (by omega) _
      | inr h=> rw [show press (release (A i'))=0 from ih _ h,map_zero,map_zero]
  intro h; exact Finset.sum_eq_zero fun i _=> h i
end YM.XSpace.Scale
