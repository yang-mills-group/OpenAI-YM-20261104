import YM.Integration.WilsonPhysicalHistoryRetainedSpringFaceRay
import YM.Integration.WilsonPhysicalHistoryRetainedSpringGramMoment

/-! Charge each of the four original oriented face visits in the measured
chamber. Repeated edges stay in the Gaussian moment on the same sample. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open MeasureTheory WilsonMeasuredPathTaylor WilsonWalkMatrixSecant
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {P : Teller G} {η r Q Y : ℝ} {X : Coat T F}

theorem fare_moment (A : Rotator P L η r Q Y X) (s : Signed) (q : ℕ) (x : Site f) (w : Walk) :
    let v:=fun z : Air f G=>collect G (pulled (angularSample F z) s)
    Integrable (fun z=>fare (v z) x w^(q+1)) X.dice ∧
      (∫ z,fare (v z) x w^(q+1) ∂X.dice)≤((w.length:ℝ)*speedPrice G L η r Q q)^(q+1) := by
  intro v
  let l:=occurrences x w
  let a (i : Fin l.length) (z : Air f G):=speed (v z) (l.get i)
  have printed (z : Air f G) : ∑ i,a i z=fare (v z) x w:=by
    change ∑ i : Fin l.length,speed (v z) (l.get i)=(l.map (speed (v z))).sum
    have perm : List.ofFn (speed (v z) ∘ l.get)=l.map (speed (v z)):=by rw [←List.map_ofFn,List.ofFn_get]
    rw [←perm,List.sum_ofFn]
    rfl
  have buy:=QLocalMeasuredPathMoments.pooled X.dice Finset.univ
    (fun _ : Fin l.length=>speedPrice G L η r Q q) a (fun _ _=>speed_price_pos ..)
    (fun i _ z=>show 0≤‖G.colorMat (v z (l.get i))‖ from norm_nonneg _)
    (fun i _=>(rotated_receipt A s q (l.get i)).1) q (fun i _=>(rotated_receipt A s q (l.get i)).2)
  simpa only [printed,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,l,length_occurrences] using buy

def faceCost (G : Gauge) (h : ℕ) (M : ℝ) : ℝ:=tracePrice G*‖(1:G.Mat)‖*(4*M)^h

theorem face_cost_nonneg (G : Gauge) (h : ℕ) {M : ℝ} (pos : 0≤M) : 0≤faceCost G h M:=by
  unfold faceCost tracePrice
  positivity

theorem measured_face (A : Rotator P L η r Q Y X) (s : Signed) (x : Site f) (a : PlaqAxes)
    (q l : ℕ) (g : ℝ) :
    let v:=fun z : Air f G=>collect G (pulled (angularSample F z) s)
    let e:=fun z : Air f G=>G.price (faceValue (field (v z) g) (x,a))-faceRay (v z) x a q g
    let M:=speedPrice G L η r Q ((q+1)*(l+1)-1)
    Integrable (fun z=>|e z|^(l+1)) X.dice ∧ (∫ z,|e z|^(l+1) ∂X.dice)≤
      (faceCost G (q+1) M*|g|^(q+1))^(l+1) := by
  intro v e M
  let w:=square a.val.1 a.val.2
  let h:=q+1
  let p:=l+1
  let u:=h*p-1
  let k:=tracePrice G*‖(1:G.Mat)‖*|g|^h
  have eqn : u+1=h*p:=Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
  have kpos : 0≤k:=by unfold k tracePrice; positivity
  have nonneg (z : Air f G) : 0≤fare (v z) x w:=by
    unfold fare
    exact List.sum_nonneg (fun a ha=>by obtain ⟨b,-,rfl⟩:=List.mem_map.mp ha; exact norm_nonneg _)
  have rawCont : Continuous (fun z : Air f G=>field (v z) g):=continuous_pi fun b=>
    G.lieExp_cont.comp (((continuous_apply b).comp (rotated_continuous F s)).const_smul g)
  have em : Continuous e:=by
    change Continuous (fun z=>G.price (travel (field (v z) g) x w)-faceRay (v z) x a q g)
    exact (G.continuous_price.comp ((continuous_travel w x).comp rawCont)).sub
      ((face_ray_continuous x a q g).comp (rotated_continuous F s))
  have each (z : Air f G) : |e z|^p≤k^p*fare (v z) x w^(h*p):=by
    have ray:=face_ray_error (v z) x a q g
    have one : 1≤((q+1).factorial:ℝ):=by exact_mod_cast Nat.factorial_pos (q+1)
    have loose : |e z|≤k*fare (v z) x w^h:=by
      apply ray.trans
      change tracePrice G*((fare (v z) x w^h*‖(1:G.Mat)‖)*|g|^h/((q+1).factorial:ℝ))≤_
      calc
        _ ≤ tracePrice G*((fare (v z) x w^h*‖(1:G.Mat)‖)*|g|^h):=
          mul_le_mul_of_nonneg_left (div_le_self (by positivity [nonneg z]) one) (by unfold tracePrice; positivity)
        _ = _:=by dsimp only [k]; ring
    calc
      _ ≤ (k*fare (v z) x w^h)^p:=pow_le_pow_left₀ (abs_nonneg _) loose _
      _ = _:=by rw [mul_pow,pow_mul]
  have paid:=fare_moment A s u x w
  have len : w.length=4:=rfl
  rw [eqn,len] at paid
  have major: Integrable (fun z=>k^p*fare (v z) x w^(h*p)) X.dice:=paid.1.const_mul _
  have meas : Integrable (fun z=>|e z|^p) X.dice:=major.mono' (em.abs.pow p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z=>by rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤|e z|^p)]; exact each z)
  refine ⟨meas,(integral_mono meas major each).trans ?_⟩
  rw [integral_const_mul]
  apply (mul_le_mul_of_nonneg_left paid.2 (pow_nonneg kpos _)).trans_eq
  change k^p*(4*M)^(h*p)=(faceCost G h M*|g|^h)^p
  rw [pow_mul,←mul_pow]
  congr 1
  unfold k faceCost
  ring

end YM.Integration.OriginalMarkedRunAction
