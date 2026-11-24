import YM.MS.ScaleForest.Icy
/-!
# Exact-at-zero-momenta projection

Use at a bridge with rank/field grade tuned to zero available external Taylor
degrees. There the **overall** MS pole can be proved absent, even if the
inputs to that bridge were made using children with nonzero counterterms.
Don't confuse these two pole operations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open scoped Topology ContDiff
variable {G : Gauge} {b : Bool} {n h ell m : ℕ} {X : Flats G}

abbrev expires (w : Legs (Shore G m)) := ∀ i∈w,i.2=0

theorem A_zero (s : ℝ) (i j : Cfield G m) : A0 G s m i j 0=0 := by
  rw [radial_log]; unfold radial City.LegsK Landau.choir; simp only [Pi.smul_apply]; split
  next he=> simp only [id_eq,Swirl.Near.bruC _ _
    (show Momentum.sq (0:SectorP m)=0 by simp [Momentum.sq]) _, smul_zero]
  exact smul_zero _

theorem expires_erase (w : Legs (Shore G m)) : expires (sail (ray w) 0) := by
  rw [ray_go]; intro i hi; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi; exact zero_smul ℝ _

variable {w : Legs (Shore G m)}

theorem expires_sr (he : expires w) (s : ℝ) : sr s w=w := by
  induction w with
  | nil=> rfl
  | cons i w ih => unfold sr; rw [List.map_cons,show ((i.1, exp s • i.2) : Shore G m)=i from
      Prod.ext rfl (Eq.trans (congr_arg (exp s • ·) (he i (by simp))) (by rw [smul_zero]; exact (he i (by simp)).symm)),
      show List.map _ w=_ from ih (fun i hi=> he _ (List.mem_cons_of_mem _ hi))]

theorem expires_sail (he : expires w) (t : ℝ) : sail (ray w) t=w := by
  rw [ray_go]
  induction w with
  | nil=> rfl
  | cons i w ih => rw [List.map_cons,ih (fun i hi=> he i (List.mem_cons_of_mem _ hi)),
      show ((i.1, t • i.2) : Shore G m)=i from ?_]; obtain hv:=he i (by simp); simp [hv]; exact Prod.ext rfl hv.symm

theorem bridge_off (s : ℝ) (he : expires w) (A B : Mob G) : bridgeG (A0 G s) A B m w = 0 := by
  unfold bridgeG; rw [scatter_congr _ w _ (fun _ _=>0) ?_]; exact map_zero (allocate ..)
  intro p q hp
  have hx (w : Legs (Shore G m)) (h : expires w) : net w=0 := by
    induction w with
    | nil=> rfl
    | cons i w ih=> rw [net_cons,ih (fun i hi=> h i (List.mem_cons_of_mem _ hi)), h i (by simp),zero_add]
  rw [hx p (fun i hi=> he i ((split_perm hp).mem_iff.mp (List.mem_append_left _ hi)))] ; simp only [neg_zero,A_zero,mul_zero, zero_mul, Finset.sum_const_zero]

-- Special threshold h, constant local Taylor extraction.
theorem weight_paid (w : Legs (Shore G m)) (he : mass w=(h:ℤ)) (U : Mob G) : Tad U h m w = U m (sail (ray w) 0) := by
  rw [t_bud U (show mass w+((0:ℕ):ℤ)=h by omega), torch_at,reading]
  simp only [iteratedDeriv_zero,Nat.factorial_zero, Nat.cast_one,inv_one,one_smul]

/-- At all-zero momenta **for this bridge**, not even the scale integral
Taylor terms affect the vanishing of the prepared amplitude. -/
abbrev at_origin (X : Flats G) (m : ℕ) (w : Legs (Shore G m)) := ∀ i z, X i z m w=0

theorem bridge_pages_zero (s : ℝ) (c : ℂ) (he : expires w) (X Y : Flats G) :
    at_origin (c • bridgePages (A0 G s) X Y) m w := by
  intro i z
  unfold bridgePages Finsupp.sum
  simp only [Finsupp.smul_apply,Pi.smul_apply,Finsupp.finsetSum_apply,Finset.sum_apply]
  rw [Finset.sum_eq_zero, smul_zero]
  intro j _; refine Finset.sum_eq_zero fun k _=> ?_; rw [Finsupp.single_apply]; split
  · exact bridge_off s he ..
  rfl

theorem off_integrate (he : expires w) (hX : at_origin X m w) (h : ℕ) : at_origin (integratePages h X) m w := by
  intro i z; rw [integrate_each]; unfold scaleIntegral; apply Tendsto.limUnder_eq
  have hh (a : ℝ) : regulated a 0 z h i (X i z) m w=0 := by
    unfold regulated finiteIntegral belowCut
    have hn (j : ℕ) : Tad (X i z) j m w=0 := by
      unfold Tad skin; split; next h=>
        rw [torch_at]; simp_rw [expires_sail he,hX]; simp [reading]
      rfl
    simp only [Pi.add_apply, plow, expires_sr he,hX,mul_zero, intervalIntegral.integral_zero,zero_add]
    split; rfl; simp_rw [Finset.sum_apply,Pi.smul_apply,hn,smul_zero,Finset.sum_const_zero]
  simp_rw [hh]; exact tendsto_const_nhds

theorem off_parade (he : expires w) (hX : at_origin X m w) (h : ℕ) (s y : ℝ) (z : ℂ) : Parade X h y s z m w=0 := by
  unfold Parade Finsupp.sum; simp_rw [Finset.sum_apply,hikeP,Pi.smul_apply,plow,expires_sr he,hX,mul_zero,smul_zero,
     Finset.sum_const_zero]

theorem bridge_no_pole {A : GraphSum G true 4} {B : GraphSum G b h} (hw : mass w=h) (z : ℂ) :
    (GraphSum.bridge (fullShell G) A B).instructions.pole z m w=0 := by
  let X := GraphSum.bridge (fullShell G) A B
  let l := sail (ray w) 0
  let f := Parade X.instructions.renorm h 0 0
  have ht : at_origin X.instructions.prep m l :=
    off_integrate (expires_erase w) (bridge_pages_zero 0 (factor b) (expires_erase w) _ _) h
  have he (s : ℂ) : f s m l = X.instructions.pole s m l := by
    unfold f Result.renorm; rw [page_add, Pi.add_apply, Pi.add_apply, Pi.add_apply,
      pureP _ X.accepted.after.back, off_parade (expires_erase w) ht, zero_add]
  obtain hv := Live.tends (show Live f from X.accepted.after.toll 0 0)
  change X.instructions.pole z m w=0
  rw [X.accepted.local_ct,weight_paid w hw]; exact coolEdge l X.accepted.after.ice
    (by simpa only [he] using hv.choose_spec m l) z
end YM.MS.ScaleForest
