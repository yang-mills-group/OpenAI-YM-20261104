import YM.RGComparison.Core16.Catkin.Hub
/-!
# Read on paths localized to any ch-color clock.
Common σ,C,Λ path account produces true real Hess loc (no g pricing yet).
Impulse response from rank-1 curl at face, forward or signed-pulled; budgets include exact uncut path counts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Catkin
open Function Filter Set Lattice Wilson Exterior RG Precision
open MeasureTheory Halo Lam Pert.Kinetic Work.F03 Lumen AnalyticBridge.VerifiedReset
open Push.Uniform StressFlux
open scoped Topology BigOperators Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {G: Gauge} {n f:Side} {σ C Λ δ w:ℝ} {u : ℝ} {i:Site n} {s:Signed} {v: G.ColorIndex} {W: PathData G}

-- `post.L` : oriented actual field in spin sum v
abbrev crest (i:Operand G n): Site n:= i.1.1
abbrev sell (s:Signed)(u:Directions G n): fieldDir G n 1:= Bid.pulled (lift1 u) s
abbrev post (s:Signed)(a:Operand G n):= sell s (compass a)

lemma compass_fee (a:Operand G n)(e: Edge (Site n)) : ‖compass a e‖ ≤ 1 :=by
    unfold compass; by_cases h:a.1=e
    · rw [← h,Pi.single_eq_same]; exact OrthonormalBasis.norm_eq_one ..|>.le
    rw [Pi.single_eq_of_ne (Ne.symm h),norm_zero]; exact zero_le_one
lemma upright (x : Directions G n) (a: ℝ) (hx : ∀ i, ‖x i‖ ≤ a) (y: Face (Per n)) : ‖faceCurl y (lift1 x)‖ ≤ 4*a:=by
    rcases y with ⟨y,p⟩; rw [faceCurl,← Exterior.fundamental,Square.cochain_square,back_wave]
    exact (norm_sub_le ..).trans ((add_le_add ((norm_sub_le ..).trans (add_le_add (hx _) (hx _))) ((norm_sub_le ..).trans (add_le_add (hx _) (hx _)))).trans_eq (by ring))
lemma cage (s:Signed)(a:Operand G n)(i : Edge (Site n)): ‖pullDir s 0 (compass a) i‖ ≤ 1 :=by
    change ‖sign s i.2 • compass a _‖ ≤ _; have he k : |sign s k|=1:= by unfold sign; split <;> simp
    rw [norm_smul,Real.norm_eq_abs,he,one_mul]; exact compass_fee ..
variable (hn:4≤ n.val)
include hn in
lemma rank (s:Signed) (a:Operand G n)(y: Face (Per n)): ‖faceCurl y (post s a)‖ ≤ 4 :=by
    dsimp only [post,sell]; rw [← converts_dir (hn:=hn)]; exact (upright _ 1 (cage s a) y).trans_eq (mul_one ..) -- upright unusedVar
lemma sent (s:Signed)(e : Edge (Site n)): separation (sendEdge s (0:Site n) e).1 (s.act e.1) ≤ 1:= by
    unfold sendEdge _root_.YM.Lattice.Step.used; split; · dsimp only; rw [Lattice.affine,add_zero,separation]; simp [pdist_step]
    dsimp only; rw [Lattice.affine, add_zero,separation]; simp [pdist]
lemma local_post (s:Signed)(a:Operand G n)(e : Edge (Site n))(h: 1 < separation (crest a) (s.act e.1)): pullDir s 0 (compass a) e=0 :=by
   change sign s e.2 • compass a _=0; unfold compass; rw [Pi.single_eq_of_ne,smul_zero]; intro he; apply h.not_ge; have hu:= sent s e; rw [he] at hu; exact hu

private lemma plus_one (i:Site n)(j:Axis) : separation (i+step j) i ≤ 1:=by rw [separation,add_comm i,add_sub_cancel_right]; exact pdist_step _
include hn
lemma local_flow (s:Signed)(a:Operand G n)(y: Face (Per n)) (h: 2 < separation (crest a) (s.act y.1)) : faceCurl y (post s a)=0:=by
    rcases y with ⟨x,p⟩; dsimp only at h
    have hy j: 1 < separation (crest a) (s.act (x+step j)) := by
        have hb:= separation_triangle (crest a) (s.act (x+step j)) (s.act x); rw [separation_signed] at hb; have hh:= plus_one x j; omega
    dsimp only [post,sell]; rw [← converts_dir (hn:=hn),faceCurl, ← Exterior.fundamental,Square.cochain_square,back_wave]; dsimp only
    have hhx (i:Axis) : pullDir s 0 (compass a) (x,i)=0:= local_post s a (x,i) (Nat.lt_trans one_lt_two h)
    have hhy (i j:Axis) : pullDir s 0 (compass a) (x+step i,j)=0:= local_post s a (x+step i,j) (hy i)
    simp only [hhx,hhy,sub_self]

-- length λ; e attenuation if |post| amplifies by exp(2α). Charge σ slot-factor for any β.
def fee (α :ℝ) := 4*Real.exp (2*α)
omit hn in
lemma fee_pos (α:ℝ):0 < fee α := by unfold fee; positivity
variable {α : ℝ} (ha:0 ≤ α)
include ha
lemma homage (s:Signed)(a:Operand G n)(x y: Site n)(p:PlaqAxes) (k:ℕ) (hx: separation y x ≤ k) : ‖faceCurl (y,p) (post s a)‖ ≤ fee α * Real.exp (α*k) * Decay α (crest a) (s.act x) := by
    by_cases h:2 < separation (crest a) (s.act y); · rw [local_flow hn s a (y,p) h,norm_zero]; have :=fee_pos α; have := decay_pos α (crest a) (s.act x); positivity
    have he : separation (crest a) (s.act x) ≤ 2+k:=by
       refine (separation_triangle _ (s.act y) _).trans ?_; rw [separation_signed]; omega
    apply (rank hn s a _).trans; unfold fee Decay; rw [mul_assoc (4:ℝ), mul_assoc (4:ℝ),← Real.exp_add,← Real.exp_add]; apply le_mul_of_one_le_right (by norm_num); apply Real.one_le_exp; have he' : (separation (crest a) (s.act x):ℝ) ≤ 2+k:=by exact_mod_cast he
    linarith only [mul_le_mul_of_nonneg_left he' ha]
lemma act (s:Signed)(a:Operand G n)(y:Face (Per n)) : ‖faceCurl y (post s a)‖ ≤ fee α * Decay α (crest a) (s.act y.1) :=by simpa only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using! homage hn ha s a y.1 y.1 y.2 0 (Pert.Kinetic.sep_self _).le

variable {p:Clip} (h:W.Bounds p σ C Λ) (he :α ≤ σ)
include h he
lemma rounds (s:Signed)(a:Operand G n)(y:Face (Per n)): ‖ellLine W y (post s a)‖ ≤ fee α * C * Decay α (crest a) (s.act y.1):= by
    let g:ℝ:= fee α *Decay α (crest a) (s.act y.1); let r:=W.row y.2; let x i:= |(r i).1| * Real.exp (σ*(r i).2.length); have hg :0 ≤ g:= (mul_pos (fee_pos _) (decay_pos ..)).le
    have hb i : ‖faceCurl (slotFace (r i).2 y.1) (post s a)‖ ≤ Real.exp (σ*(r i).2.length)*g:= by
         refine (homage hn ha s a y.1 (wrap n (r i).2.offset + y.1) (r i).2.plaq (r i).2.length ((separation_comm ..).trans_le (Work.E04.slot_separation (r i).2 _))).trans ?_ -- RHS infers hx?
         rw [mul_right_comm, mul_comm _ (Real.exp (α*_))]; exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))) hg
    have hs:= (ellLine_summable W h y (post s a)).norm; have hv: SumBudget x C:=h.rows y.2
    have hf i : ‖(r i).1 • faceCurl (slotFace (r i).2 y.1) (post s a)‖ ≤ x i*g:= by rw [norm_smul,Real.norm_eq_abs]; unfold x; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)
    exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hf (hv.2.1.mul_right g)).trans ((tsum_mul_right).trans_le ((mul_le_mul_of_nonneg_right hv.2.2 hg).trans_eq (by unfold g; ring))))

omit ha h he
lemma sells_add (s:Signed)(a b:Directions G n): sell s (a+b)=sell s a+sell s b:=by dsimp only [sell]; rw [← converts_dir (hn:=hn),← converts_dir (hn:=hn),← converts_dir (hn:=hn),map_add]; rfl
omit hn
lemma act_add (a b:fieldDir G n 1)(y:Face (Per n)): faceCurl y (a+b)=faceCurl y a+faceCurl y b:=by 
    rcases y with ⟨x,k⟩
    simp only [faceCurl,← Exterior.fundamental, Square.cochain_square]
    unfold Exterior.collect; simp only [Pi.add_apply]; abel
include h in
lemma ell_add (u v: fieldDir G n 1) (y: Face (Per n)) : ellLine W y (u+v)=ellLine W y u+ellLine W y v:= by unfold ellLine; simp_rw [act_add,smul_add]; exact (ellLine_summable W h y u).tsum_add (ellLine_summable W h y v)
end YM.RGComparison.Core16.Catkin
