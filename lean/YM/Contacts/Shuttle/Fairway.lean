import YM.Contacts.Shuttle.Frost
import YM.Contacts.Shuttle.Surf
/-! # torus evaluating Ward through the charges -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 240000
noncomputable section
namespace YM.Contacts.Shuttle.Tide
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Labels Source Drops Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor MultiNext.SignedSource Pattern Broadcast
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X Y ι κ Z E : Type}[Fintype ι][NormedAddCommGroup E][NormedSpace ℝ E]{s:ℝ≥0}{b c:ℝ}{h k n:ℕ}(m:Side) (H:Hol G)
abbrev Dyes (G:Gauge):= Loc G 1
def place (U:Draft G h)(x:E4) := glow G.Color h U.1 x
def coloredAt (m:Side)(U:Draft G h)(x:Site m) := G.lieExp (place U (xyz (lift x)))
def frameAt (H:Hol G)(m:Side)(U:Draft G h)(x:Edge (Site m)): G.El:= H.links h (expand h U.2) 1 (lift x.1,x.2)
def raft (H:Hol G)(m:Side)(a:Draft G h) := Lattice.gauge (coloredAt m a) (frameAt H m a)
def timber (m:Side)(x: Site m)(i:Axis) : Draft G h→L[ℝ] Panel G h :=
    let K (x:Site m): Draft G h→L[ℝ] G.Color := (glance G.Color h (xyz (lift x))).comp (ContinuousLinearMap.fst ℝ _ _)
    (K x).prod (((K (x+Lattice.step i)-K x)).prod ((tempo (xyz (lift x)) i).comp (ContinuousLinearMap.snd ℝ _ _)))
lemma timber_form (v:Draft G h)(x:Edge (Site m)): timber m x.1 x.2 v=(place v (xyz (lift x.1)),place v (xyz (lift (x.1+Lattice.step x.2)))-place v (xyz (lift x.1)),tempo (d:=h) (xyz (lift x.1)) x.2 v.2):=rfl
lemma raft_base (h:ℕ) : raft H m (0:Draft G h)=1:= by
   funext i; let F:= frameAt H m (0:Draft G h); have he:F i=1:= by apply G.mat_injective; unfold F frameAt; rw [Pattern.stem,G.mat_one]; change Pattern.run G h (tempo (G:=G) (d:=h) _ _ 0)=_; rw [show tempo (G:=G) (d:=h) (xyz (lift i.1)) i.2 0=0 from (tempo (G:=G) (d:=h) (xyz (lift i.1)) i.2).map_zero, (Pattern.endpoint ..).2.1]
   have hu : coloredAt m (0:Draft G h)=1:= by funext i; unfold coloredAt place; simp
   change Lattice.gauge _ F i= _; rw [hu]; simp [Lattice.gauge,he]; try rfl
lemma raft_port (h:ℕ): Army (fun u:Draft G h=> raft H m u) 0 := by
   refine Army.slant ?_ fun i=>?_ -- argument order?
   · intro i; let U: Draft G h→L[ℝ] G.Color:= (glance G.Color h (xyz (lift i))).comp (ContinuousLinearMap.fst ℝ _ _); exact (G.exp_jet.comp U.contDiff).contDiffAt
   let X: Draft G h→L[ℝ] Fiber G h:= (tempo (xyz (lift i.1)) i.2).comp (ContinuousLinearMap.snd ℝ _ _); simp_rw [frameAt, Pattern.stem]; exact (ContDiffAt.comp (f:=X) (g:=Pattern.run G h) _ (by rw [X.map_zero]; exact (Pattern.endpoint ..).1) X.contDiff.contDiffAt)
-- Period-reading assembly (abs faults estimated elsewhere)
def north (H:Hol G)(m:Side) (v:Draft G h): Link G m:= content (raft H m v)
lemma north_ship (v:Draft G h)(x:Site m)(a:Axis)(i:G.ColorIndex): north H m v (x,coord a,i)=stereo G h (timber m x a v) i:= by
   let w:Edge (Site m):=(x,a); let U:=raft H m v; let b:= timber m x a v; change (arm G m 1 (content U) (x,coord a)) i=_; rw [content_at]; change G.plog (G.mat (Lattice.gauge _ (frameAt H m v) w)) i=_; unfold Lattice.gauge; simp_rw [G.mat_mul,G.mat_inv]; unfold frameAt; rw [Pattern.stem]; apply congr_arg (fun z:G.Mat=> G.plog z i); change G.mat (G.lieExp b.1)*Pattern.run G h b.2.2*star (G.mat (G.lieExp (place v (xyz (lift (x+Lattice.step a)))))) = _; rw [show place v (xyz (lift (x+Lattice.step a)))=b.1+b.2.1 from (add_sub_cancel ..).symm] -- check
lemma north_diff (h:ℕ): ContDiffAt ℝ ω (north (h:=h) H m) 0:= (raft_port m H h).logL (raft_base m H h)
lemma north_zero (h:ℕ) : north H m (0:Draft G h)=0:= by rw [north,raft_base]; simp
lemma north_turn (v:Fin k→Draft G h)(x: Site m)(a:Axis)(i:G.ColorIndex) : iteratedFDeriv ℝ k (north H m) 0 v (x,coord a,i)=
   (iteratedFDeriv ℝ k (stereo G h) 0 (timber m x a ∘ v)) i:= by
    let A: Link G m →L[ℝ] ℝ:= ContinuousLinearMap.proj (x,coord a,i); let B:= EuclideanSpace.proj (𝕜:=ℝ) i; let P: Draft G h→L[ℝ] Panel G h:= timber m x a; have hp : A ∘ north (h:=h) H m=B ∘ stereo G h ∘ P:= funext fun i=>north_ship ..; have hm:=A.iteratedFDeriv_comp_left (north_diff m H h) (i:=k) le_top; have hd:= scripts G h
    have hv : ContDiffAt ℝ ω (stereo G h ∘ P) 0:= ContDiffAt.comp _ (show ContDiffAt ℝ ω (stereo G h) (P 0) from P.map_zero.symm ▸ hd.1) P.contDiff.contDiffAt; rw [hp,B.iteratedFDeriv_comp_left hv] at hm; refine (DFunLike.congr_fun hm v).symm.trans ?_; exact congr_arg B (DFunLike.congr_fun (Next.Foundations.jets_linear P (k:=k) (hd.1.of_le le_top)) v); exact le_top
lemma unfolds_wood (v:Draft G h){m:ℕ→Side}(hm:Tendsto (fun j=>(m j).val) atTop atTop) (x: Cover)(a:Axis): ∀ᶠ i in atTop,timber (m i) (wrap (m i) x) a v=shape (G:=G) (d:=h) (xyz x) a v:= by
   filter_upwards [eventually_unfold m hm x, eventually_unfold m hm (x+Lattice.step a)] with i hi ht; rw [map_add] at ht; let w:Edge (Site (m i)):= (wrap (m i) x,a); change timber _ w.1 w.2 _=_; rw [timber_form _ _ w]; change (place v (xyz (lift (wrap (m i) x))),place v (xyz _) - place v (xyz (lift (wrap (m i) x))),tempo (xyz (lift (wrap (m i) x))) a v.2)=_; rw [hi,show lift (w.1+Lattice.step w.2)=x+Lattice.step a from (by simpa [w] using ht),xyz_step]; rfl
end YM.Contacts.Shuttle.Tide
