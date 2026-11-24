import YM.FormalBulk08.Flat.Ledger

/-!
The centered inverse and price include gauge modes. Convert to the actual
TREE slice. Absolute fine logs here, not displacements from a coarse
background. Work at any period with true cochain coordinates & counting
volumes. Geometry of cover reindexing and the actual Gaussian use are
separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary Tree
open scoped Topology BigOperators Matrix
variable {G : Gauge} {P : Patch} {K : KernelChoices} {c f : Side} {S : StepData c f} {j : ℕ}

lemma mat_confirm {a b : Type} [Fintype b] [DecidableEq b] {A B : Matrix a b ℝ} (h : ∀ v, A*ᵥ v=B*ᵥ v) : A=B := by
  ext i j; simpa [Matrix.mulVec_single] using congr_fun (h (Pi.single j 1)) i

/-- Coordinate kill below. -/
def lives (F : Forest S.ratio) (x : Lines G f 1) := (x.1,axisEquiv.symm x.2.1)∉F.trunks
abbrev Alive (G : Gauge) (S : StepData c f) (F : Forest S.ratio) := Subtype (@lives G c f S F)
instance lifeDecide (F : Forest S.ratio) (x : Lines G f 1) : Decidable (lives F x) := by unfold lives; infer_instance

variable (G S)
def dropRoot (F : Forest S.ratio) : Matrix (Alive G S F) (Lines G f 1) ℝ := (1:Matrix (Lines G f 1) _ ℝ).submatrix (fun i=>i.val) id
variable {S G}
lemma drop_apply (F : Forest S.ratio) (v : Lines G f 1→ℝ) (i : Alive G S F) :
    (dropRoot G S F*ᵥ v) i=v i.val := congr_fun (Matrix.one_mulVec v) i.val
lemma bring_alive (F : Forest S.ratio) (x : Alive G S F→ℝ) (i : Alive G S F) :
    ((dropRoot G S F)ᵀ *ᵥ x) i.val=x i := by
  simp [Matrix.mulVec,dotProduct, Matrix.one_apply, dropRoot, Subtype.val_inj,ite_mul]
lemma bring_dead (F : Forest S.ratio) (x : Alive G S F→ℝ) {i : Lines G f 1} (h : ¬lives F i) :
    ((dropRoot G S F)ᵀ *ᵥ x) i=0 := by
  have he (j : Alive G S F) : j.val≠i := fun e=> h (e ▸ j.property)
  simp [Matrix.mulVec,dotProduct, dropRoot,he]
lemma returns (F : Forest S.ratio) : dropRoot G S F*(dropRoot G S F)ᵀ=1 := by
  apply mat_confirm; intro v; ext i; rw [← Matrix.mulVec_mulVec,drop_apply, bring_alive,Matrix.one_mulVec]
lemma paste (F : Forest S.ratio) (x : Lines G f 1→ℝ) (h : ∀ i, ¬ lives F i → x i=0) :
    (dropRoot G S F)ᵀ*ᵥ ((dropRoot G S F)*ᵥ x)=x := by
  ext i
  by_cases ht : lives F i
  · exact (bring_alive F _ ⟨i,ht⟩).trans (drop_apply ..)
  exact (bring_dead F _ ht).trans (h i ht).symm

variable (S)
def trails (F : Forest S.ratio) : Matrix (Body 0 f) (Body 1 f) ℝ := LinearMap.toMatrix' (LinearMap.pi fun i : Body 0 f => integralLink i.1 (F.hike i.1))
def apices : Matrix (Body 0 f) (Body 0 c) ℝ := LinearMap.toMatrix' (LinearMap.pi fun i : Body 0 f => (LinearMap.proj (S.ratio.parent i.1,vac) : form 0 c→ₗ[ℝ] ℝ))
def fetch : Matrix (Body 0 c) (Body 0 f) ℝ := LinearMap.toMatrix' (LinearMap.pi fun i : Body 0 c => (LinearMap.proj (S.ratio.embed i.1,i.2) : form 0 f→ₗ[ℝ] ℝ))
variable {S}
lemma trail_map (F : Forest S.ratio) (x) (v) : (trails S F*ᵥ x) v=integralLink v.1 (F.hike v.1) x := by rw [trails,LinearMap.toMatrix'_mulVec]; rfl
lemma peaks (x : form 0 c) v : (apices S *ᵥ x) v = x (S.ratio.parent v.1,vac) := by rw [apices,LinearMap.toMatrix'_mulVec]; rfl
lemma fetch_lands (v) : fetch S*ᵥ v=centered S v := by rw [fetch,LinearMap.toMatrix'_mulVec]; rfl

variable (G S)
/-- Solve for a gradient on the whole root forest. -/
def lead (F : Forest S.ratio) := patron G (trails S F)*butt G c f - patron G (apices S)*(patron G (fixRoot S)*butt G c f+brim G c f)
/-- Move to the rooted slice output in all link coordinates (zeros on tree links). -/
def imprint (F : Forest S.ratio) := butt G c f + patron G (d 0 f)*lead G S F
/-- Keep only live variables. -/
def hang (F : Forest S.ratio) := dropRoot G S F*imprint G S F
variable {G S}

section properties
def atPaint {j} (a : Corn (Lines G c j)) (k : G.ColorIndex) : form j c := fun i=> a (i.1,i.2,k)
lemma paint_eats {j r} (A : Matrix (Body j c) (Body r f) ℝ) (v : Lines G f r → ℝ) (k) :
    atPaint (patron G A*ᵥ v) k=A *ᵥ atPaint v k := by rw [patron_fee]; rfl
lemma roots_pictured (F : Forest S.ratio) (x : Lines G f 1 → ℝ) (i : Lines G f 0) :
    (patron G (trails S F)*ᵥ x) i=integralLink i.1 (F.hike i.1) (atPaint x i.2.2) := by
  exact (congr_fun (paint_eats (trails S F) x i.2.2) (i.1,i.2.1)).trans (trail_map ..)
lemma peak_seen (x : Lines G c 0→ℝ) v :
    (patron G (apices S)*ᵥ x) v=x (S.ratio.parent v.1,vac,v.2.2) := (congr_fun (paint_eats _ _ v.2.2) (v.1,v.2.1)).trans (peaks _ _)
lemma lead_price (F : Forest S.ratio) (a : Bodies G c f → ℝ) v :
    let y:= butt G c f*ᵥ a
    (lead G S F*ᵥ a) v=integralLink v.1 (F.hike v.1) (atPaint y v.2.2) - (patron G (fixRoot S)*ᵥ y + brim G c f*ᵥ a) (S.ratio.parent v.1,vac,v.2.2) := by
  intro y
  simp only [lead,Matrix.sub_mulVec,← Matrix.mulVec_mulVec,Matrix.add_mulVec,Pi.sub_apply]; rw [roots_pictured,peak_seen]
lemma dead_tree (F : Forest S.ratio) (a : Bodies G c f → ℝ) (i : Lines G f 1) (hi : ¬lives F i) :
    (imprint G S F *ᵥ a) i=0 := by
  obtain ⟨r,d,k⟩:=i; obtain ⟨x,rfl⟩:=axisEquiv.surjective d
  simp only [lives,axisEquiv.symm_apply_apply, Classical.not_not] at hi
  have hg :=(F.trunk_mem_iff _).1 hi
  obtain ⟨v,hv,h⟩:=hg
  let y:=butt G c f*ᵥ a
  let u:=lead G S F*ᵥ a
  let p:= patron G (fixRoot S)*ᵥ y + brim G c f*ᵥ a
  have hu w : u (w,vac,k)=integralLink w (F.hike w) (atPaint y k)-p (S.ratio.parent w,vac,k) := lead_price F a _
  have H:= F.stays v hv
  rw [imprint, Matrix.add_mulVec,Pi.add_apply, ← Matrix.mulVec_mulVec]
  change y _+ (patron G (d 0 f)*ᵥ u) _=_
  rw [patron_fee,← first_uniform]; unfold gradientA
  simp only [LinearMap.pi_apply,LinearMap.sub_apply,LinearMap.proj_apply,axisEquiv.symm_apply_apply]
  have ht : F.hike v= F.up v :: F.hike (v+(F.up v).vec):= by rw [Forest.hike,dif_pos hv]
  cases he : F.up v with
  | mk b s =>
    rw [he] at H h
    cases s
    · simp only [Step.used,Bool.false_eq_true,↓reduceIte,Prod.mk.injEq] at h
      rw [← h.1,← h.2, hu, hu, show F.hike v=_ from ht,he]
      change S.ratio.parent (v+step b)=_ at H
      rw [H]
      unfold integralLink; dsimp; unfold atPaint; simp [linkSum,Step.used,Step.vec]
    · simp only [Step.used,↓reduceIte,Prod.mk.injEq] at h
      rw [← h.1,← h.2,sub_add_cancel,hu,hu,show F.hike v=_ from ht,he]
      rw [Step.vec, if_pos rfl, ← sub_eq_add_neg] at H
      rw [H]
      unfold integralLink; dsimp
      -- simplify step precisely here
      unfold atPaint; simp [linkSum,Step.used,Step.vec,sub_eq_add_neg]

lemma inject_out (F : Forest S.ratio) : (dropRoot G S F)ᵀ* hang G S F = imprint G S F := by
  apply mat_confirm; intro v; simp only [hang,← Matrix.mulVec_mulVec]; exact paste F _ (dead_tree F v)

lemma lead_root (F : Forest S.ratio) : patron G (fetch S)*lead G S F= -(patron G (fixRoot S)*butt G c f+brim G c f) := by
  apply mat_confirm; intro v; rw [← Matrix.mulVec_mulVec]
  funext ⟨a,i,k⟩; rw [vac_only i]
  have hh := paint_eats (fetch S) (lead G S F*ᵥ v) k
  rw [fetch_lands] at hh
  change atPaint (patron G (fetch S) *ᵥ (lead G S F*ᵥ v)) k (a,vac) = _
  rw [hh]; unfold centered atPaint
  rw [show (lead G S F *ᵥ v) _ =_ from lead_price F v (S.ratio.embed a,vac,k)]; rw [Ratio.embed_parent, Forest.hike, dif_neg (show ¬leaf S.ratio _ by simp [leaf, Ratio.embed_parent])]; change 0-_= _; rw [Matrix.neg_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,zero_sub]; rfl
lemma patron_zero {c f : Side} (G : Gauge) (r l : ℕ) : patron G (0:Matrix (Body r c) (Body l f) ℝ)=0 := by
  apply mat_confirm; intro v
  rw [patron_fee,Matrix.zero_mulVec]; ext i; unfold uniformM; dsimp; rw [Matrix.zero_mulVec]; rfl
lemma patron_plus {j t} (G : Gauge) (A B : Matrix (Body j c) (Body t f) ℝ) : patron G (A+B)=patron G A+patron G B := by
  apply mat_confirm; intro v; rw [Matrix.add_mulVec,patron_fee,patron_fee,patron_fee]; ext i; unfold uniformM; dsimp; rw [Matrix.add_mulVec]; rfl
lemma hits_tree (F : Forest S.ratio) : patron G (probe S)*imprint G S F = -fortune G S := by
  let d₀ := d 0 f
  have hm : probe S*d 0 f=d 0 c*fetch S := by
    apply mat_confirm; intro v; simp only [← Matrix.mulVec_mulVec, root_gradient,fetch_lands]
  rw [imprint, Matrix.mul_add, ← Matrix.mul_assoc, ← patron_mul,hm,patron_mul, Matrix.mul_assoc,_root_.YM.FormalBulk08.Flat.lead_root]
  unfold fortune; rw [probe,patron_plus, Matrix.add_mul, patron_mul, Matrix.mul_assoc]; unfold bondsM
  rw [Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_add]; abel
lemma base_tree (F : Forest S.ratio) (K : Matrix (Body 2 f) (Body 2 f) ℝ) :
    let X:=patron G (Precision.K K)
    (imprint G S F)ᵀ*X*imprint G S F=(butt G c f)ᵀ*X*butt G c f := by
  intro X
  let Y:=patron G (d 0 f)
  have he : X*Y=0 := by unfold X Y; rw [← patron_mul, Precision.K_kills, patron_zero]
  have ht : Yᵀ*X=0 := by unfold X Y; rw [← patron_star,← patron_mul,Precision.K_orthogonal,patron_zero]
  change (butt G c f + Y*_)ᵀ*X*(butt G c f+Y*_)=_
  rw [Matrix.transpose_add,Matrix.transpose_mul,Matrix.add_mul, Matrix.mul_assoc _ Yᵀ X,ht,Matrix.mul_zero,add_zero,Matrix.mul_assoc,Matrix.mul_add,← Matrix.mul_assoc X,he,Matrix.zero_mul,add_zero,Matrix.mul_assoc]
end properties
end YM.FormalBulk08.Flat
