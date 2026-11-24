import YM.XSpace.Mu
import YM.Push.LOOP_COEFFICIENT.Frequency
/-!
# Full signed symmetry on unconditioned operators at first positive degree

So the temporary compensation can be taken H-equivariant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Hoops
open Filter Set Function Lattice Chart2 Mu Outline Sail JetGauge Next.Rank.Normal Contraction Finsupp Further.FreeCovariance.KP
open scoped Topology BigOperators ComplexConjugate
variable {R:Type*} [AddCommGroup R] [One R] {G:Gauge} {n:Side}
variable (s:Signed)
omit [One R] in
def basePerm (s:Signed): Equiv.Perm (Four R):=⟨s.act,s⁻¹.act,s.inv_act,s.act_inv⟩
lemma step_act (i:Axis): s.act (R:=R) (step i)= if s.flip i then -step (s.perm i) else step (s.perm i):=by rw [← Step.vec_pos i,← Step.vec_rotate]; simp [Step.vec,Step.rotate,posDir]
lemma count_square (p:Site n): Potential.normSquare (s.act p)= Potential.normSquare p:=by
  unfold Potential.normSquare; rw [← Equiv.sum_comp s.perm]; refine Finset.sum_congr rfl fun i _=>?_ ; have hh:= Push.Loops.cell_dual s p (step i); rw [step_act] at hh; unfold Potential.q; split_ifs at hh
  · rw [Bloch.cell_inverse,← Bloch.cell_bar] at hh; rw [← hh,← show starRingEnd ℂ 1=1 from map_one _,← map_sub,Complex.norm_conj]; simp
  rw [hh]
lemma guide (x:Site n): Potential.Gc n (s.act x) = Potential.Gc n x:=by
  unfold Potential.Gc; congr 1; rw [← Equiv.sum_comp (basePerm s)]; exact Finset.sum_congr rfl fun i _=> congr_arg₂ (·/·) (Push.Loops.cell_dual s i x) (congr_arg (fun k:ℝ=>(k:ℂ)) (count_square s i))
lemma cloud (x:Cover): Sail.cover (s.act x)= Sail.cover x:=by
  have he (n:Side): Sail.seen [] n (s.act x)= Sail.seen [] n x:= by rw [Sail.seen_bare,Sail.seen_bare,← Lattice.wrap_signed,guide]
  exact congr_arg Complex.re (tendsto_nhds_unique ((Sail.toward [] Top.side Top.grows (s.act x)).congr (fun i=> he (Top.side i))) (Sail.toward [] Top.side Top.grows x))

def swing (e: Edge (Four R)): Edge (Four R):=((posDir e.2).rotate s).used (s.act e.1)
def spins (j:Axis):ℝ:= if s.flip j then -1 else 1
def incline (A:LogLinks R G)(e:Edge (Four R)):= spins s e.2 • A (swing s e)
lemma hoist (A:LogLinks R G)(t:ℝ): (fun e=> G.lieExp (t • incline s A e))=Lattice.pull s 0 (fun e=> G.lieExp (t • A e)):=by
  funext e; unfold incline spins swing Lattice.pull Step.read Step.rotate posDir affine; simp only [Bool.false_xor,add_zero]; split_ifs <;> simp [Work.F03.exp_neg_color]
def terms (j:Bone G ℤ): Bone G ℤ →₀ ℂ:= Finsupp.single (swing s j.1,j.2) (spins s j.1.2:ℂ)
def weave : Stamp G →ₐ[ℂ] Stamp G:= exchange (terms s)
lemma weave_pit (A: LogLinks ℤ G)(u:Stamp G): pit A (weave s u)=pit (incline s A) u:=by
  unfold weave pit; rw [reads_val, show reads (terms s) (numbers A)=numbers (incline s A) from funext (fun i=>by simp [numbers, incline,terms,reads])]
lemma weave_root : scope (terms s) (Mu.root G)= Mu.root G:=by
  apply Symmetric.ext; funext i j; change treats _ (terms s i) (terms s j) =_; unfold terms; rw [treats_single]; change ((spins s j.1.2:ℂ)) *_*coal _ _ _= coal _ i j; unfold coal
  rcases i with ⟨⟨x,f⟩,a⟩; rcases j with ⟨⟨y,g⟩,b⟩; by_cases H:f=g; subst g
  · cases he: s.flip f <;> simp [he, terms, swing, spins, Step.used, Step.rotate, posDir, ← Signed.act_sub, cloud]
  cases he:s.flip f <;> cases hp: s.flip g <;> simp [H,he,hp,swing,Step.used,Step.rotate,posDir]
lemma weaves (p:Stamp G): E (Mu.root G) (weave s p)= E (Mu.root G) p:=by rw [weave,wets,weave_root,show reads (terms (G:=G) s) 0=0 from funext fun i=>by simp [reads]]
lemma weaves_V (p: Face ℤ): weave s (V3 G p)= V3 G (Face.send s 0 p):=by
  apply same; intro A; rw [weave_pit,price_at,price_at]; apply congr_arg; let L (A:LogLinks ℤ G) (t:ℝ) (i:Edge Cover):= G.lieExp (t • A i); rw [← diagnostic_price p (L (incline s A)) _ (fun e=> Fits.along_a ..), ← diagnostic_price _ (L A) _ (fun e=> Fits.along_a ..)]; congr 1; funext t; rw [show L (incline s A) t= _ from hoist s A t]; exact Face.send_price (L A t) p s 0 G.price G.price_inv (fun k g=> G.price_conj g k)

def phase (q:PlaqAxes): Equiv.Perm (Four R):= Equiv.trans (basePerm s) (Equiv.addRight (Face.send s 0 (0,q)).1)
lemma rises (q:PlaqAxes)(x:Four R): Face.send s 0 (x,q)=(phase s q x,PlaqAxes.transform s q):=by
  unfold phase PlaqAxes.transform Face.send Face.lower atFace; simp only [Equiv.trans_apply, Equiv.coe_addRight,Signed.act_zero,affine,add_zero,zero_add]; change (_,PlaqAxes.rotate s q)=(s.act x + _,PlaqAxes.rotate s q); congr 1 <;> abel
end YM.XSpace.Hoops
