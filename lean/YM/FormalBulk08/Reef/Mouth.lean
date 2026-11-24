import YM.FormalBulk08.Reef.Cake

/-! Shifted-slice Hessian exactly for the prescription. θ fixed germ. V ranges over
coarse link and Color parameters, no corner zero omission. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Reef
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free Work.F08 Work.F05 Stationary Tree Wilson
open Series Jets Wick Orb PowerSeries Matrix UVExtension.Free
open scoped Topology BigOperators Matrix ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Patch} {K : KernelChoices} {t j : ℕ}

def graft (F : Forest S.ratio) : Rays (Pine G S F⊕wire G c) → Rays (Glob G c f) := fun i=> Sum.elim (offer G F (i ∘ Sum.inl)) (i ∘ Sum.inr)
lemma graft_receipt (F : Forest S.ratio) : ContDiffAt ℝ ω (graft F (G:=G)) 0 := by
  refine contDiffAt_pi.mpr fun i=>?_
  cases i with
  | inl i=>
     exact (contDiffAt_pi.mp (show ContDiffAt ℝ ω (fun x:Rays (Pine G S F⊕wire G c)=>offer G F (x ∘ Sum.inl)) 0 from
        ((offer G F).contDiff.contDiffAt.comp (f:=fun x:Jets.Rays (Pine G S F⊕wire G c)=> x ∘ Sum.inl) 0 (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..)))) i
  | inr i=> exact contDiffAt_apply ..
lemma graft_linear (F : Forest S.ratio) (a : Rays (Pine G S F⊕wire G c)) (b : ℝ) : graft F (b•a)=b•graft F a := by
   funext i;cases i with
   | inr i=> rfl
   | inl i=> exact congr_fun (map_smul (offer G F) b (a ∘ Sum.inl)) i
@[simp] lemma graft_origin (F : Forest S.ratio) : graft F (G:=G) 0=0 := by nth_rw 1 [← zero_smul ℝ (0:Rays (Pine G S F⊕wire G c))]; rw [graft_linear,zero_smul]

lemma motor_linear {I V : Type*} [Fintype I] [Fintype V] (F : Jets.Rays V→Jets.Rays I) (H : ContDiffAt ℝ ∞ F 0) (hf : ∀ (b : ℝ) a,F (b•a)=b•F a) (x : Jets.Rays V)(i:I): traceP x (coeff 0 (motor F i))= F x i := by
   have hh:=fixed_path x (fun v=>F v i) (coord_diff _ H i)
   have hg : glimpse x (paste (fun v=>F v i))=X^1*C (F x i) := unique_gaze hh (by simpa only [hf, pow_one,Pi.smul_apply,smul_eq_mul,pow_one] using gaze_leaf (F x i) 1)
   simp_rw [motor,after_one,←glimpse_coeff,hg];simp
lemma attested (F : Forest S.ratio) (W : Pap (Glob G c f)) (x : Jets.Rays (Pine G S F⊕wire G c)) : traceP x (coeff 0 (roam ℝ (motor (graft F)) W))=traceP (graft F x) (coeff 0 W) := by
   rw [roam_first]; generalize coeff 0 W=z
   have hv i := motor_linear (graft F (G:=G)) ((graft_receipt F).of_le le_top) (fun i j=>graft_linear F j i) x i
   unfold traceP at *; induction z using MvPolynomial.induction_on with
   | C c=>simp
   | add p q hp hq=>simp_rw [map_add,hp,hq]
   | mul_X p i hp=>simp_rw [map_mul,MvPolynomial.aeval_X,hv,hp]

def sap (F : Forest S.ratio) (P : ChartRatio G) : Jets.Rays (Pine G S F)→ℝ := fun x=> Work.F05.toll F P (stand G F x)
lemma sap_root (F : Forest S.ratio) (P : ChartRatio G) (h : LocalRatio P) : sap F P 0=1 := by simp [sap,Work.F05.toll,h.anchored]
lemma sap_smooth (F : Forest S.ratio) (P : ChartRatio G) (h : LocalRatio P) : ContDiffAt ℝ ∞ (sap F P) 0 := by
   let f:=fun i:F.Free=> fun z:Rays (Pine G S F)=>P.J (stand G F z i)
   convert! drawing f Finset.univ (fun i _=>?_) using 1
   · ext; simp [sap,Work.F05.toll,f,Finset.prod_apply]
   apply ContDiffAt.comp _ _ (contDiffAt_pi.mp (stand G F).contDiff.contDiffAt i)
   simp; exact (h.germ _ (Metric.mem_ball_self h.patch)).of_le le_top

variable (F : Forest S.ratio)
def vacuumU (k : S.Choices) (p : Pap (wire G f)) : Pap (Glob G c f) := PowerSeries.map (MvPolynomial.rename Sum.inl).toRingHom p-noisePin S k
def flush (k : S.Choices) (P : ChartRatio G) (p : Pap (wire G f)) := roam ℝ (motor (graft F (G:=G))) (vacuumU k p)+halo (sap F P) (wire G c)
lemma halo_zero (P : ChartRatio G) (h : LocalRatio P) : coeff 0 (halo (sap F P) (wire G c))=0 := by rw [Jets.halo,coeff_map,covelog_rank (by rw [paste_first,sap_root F P h,map_one]),map_zero]

lemma in_value (hp : S.patch.Branches S.kernel G) (k : S.Choices) (p : Pap (wire G f)) (x : Rays (Glob G c f)) : traceP x (coeff 0 (vacuumU k p)) = traceP (x ∘ Sum.inl) (coeff 0 p)-clapBill S x x/2 := by
   rw [vacuumU,map_sub,←clap_value S hp k]; unfold traceP; rw [map_sub,coeff_map]; simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe, MvPolynomial.aeval_rename]

variable (G K)
def kernelP (k : ℝ) (V : Train j) (c : Side) := patron G (Precision.K ((pink k V).acts c))
def pMean (U : Flight j t) (c : Side) (F : Forest (Flat.primary U.patch K c).ratio) := Flat.rawMean G (Flat.primary U.patch K c) F (installed (Flat.primary U.patch K c).ratio (Flight.duo K.penalty U).A0)

lemma baked (P : Flight j t) (c : Side) (F : Forest (Flat.primary P.patch K c).ratio) (hp : 4≤t) (hu : P.patch.Branches K G) (ρ : ChartRatio G) (hr : LocalRatio ρ) :
     let S:=Flat.primary P.patch K c; let V:= pMean G K P c F; let Z:=kernelP G K.penalty P.wing (c*P.patch.L); let z:=kernelP G K.penalty P.land c
     ∀ (k : S.Choices) (T : Saddle ℝ (Pine G S F)), T.P= Flat.testPrecision G S F P.wing →
       ∀ (p : Pap (wire G (c*P.patch.L))), coeff 0 p=crunch Z → Solved ⟨T,crunch z,draught V⟩ (flush F k ρ p) := by
   intro S V Z z k T hT p hx
   let H : Hull (Pine G S F) (wire G c):=⟨T,crunch z,draught V⟩
   apply duet; intro x y
   rw [toInk_value x y H,flush,map_add,halo_zero F ρ hr,add_zero,attested,in_value hu k,hx,map_add, levelDp,duplex_C]
   let a:=V*ᵥ y
   let u:=x+a
   let Q:=(Flat.dropRoot G S F)ᵀ
   let B:=Qᵀ*Z*Q
   let e:= patron G (Precision.probe S)
   let Y:=e*Q
   have he : graft F (Sum.elim (fun i => x i + traceP y (H.drift i)) y) = Sum.elim (Q*ᵥ u) y := by rw [show (fun i => _) =u from ?_]
                                                                                                        ; rfl
                                                                                                        ; exact congr_arg (x+·) (draught_fee V y)
   rw [he,crunch_value,crunch_value,trace_base]
   have hP : T.P=B+K.penalty • (Yᵀ*Y) := hT
   have hs : T.Pᵀ=T.P := by ext i j; exact T.valid _ _
   obtain ⟨h,h'⟩:=Flat.normal G P c F hp (K:=K)
   have hy : Vᵀ*B*V+K.penalty • ((1-Y*V)ᵀ*(1-Y*V))=z := by
      change (Q*V)ᵀ * Z * (Q*V)+K.penalty • ((1-e*(Q*V))ᵀ*(1-e*(Q*V)))=z at h'
      rw [←h']; simp only [B,Y,Matrix.transpose_mul,Matrix.mul_assoc]
   have hh := additive_balance K.penalty T.P B Y V z x y hP hs (hT.symm ▸ h) hy
   have hq : dotProduct u (B*ᵥ u)=dotProduct (Q*ᵥ u) (Z *ᵥ (Q*ᵥ u)) := by unfold B; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
   change dotProduct u (B*ᵥ u)+K.penalty * dotProduct (y-Y*ᵥ u) (y-Y*ᵥ u) = _ at hh
   rw [hq,show Y*ᵥ u=e*ᵥ (Q*ᵥ u) from (Matrix.mulVec_mulVec u e Q).symm] at hh
   change - (dotProduct (Q*ᵥ u) (Z*ᵥ(Q*ᵥ u))) /2-K.penalty * dotProduct (y-e*ᵥ (Q*ᵥ u)) (y-e*ᵥ (Q*ᵥ u))/2= -(dotProduct x (T.P *ᵥ x)) / 2 + _
   linarith only [hh]
end YM.FormalBulk08.Reef
