import YM.OPE.Compatible.Begun.Rims
/-!
# Point extraction F0 exact. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m:ℕ}
abbrev CurlV (A:Mat I)(n:ℕ) [Fintype I]:= fixExp (opus A) (-(1/2:ℝ)) n
lemma rentBase (P:Flight i j)(h:f.val=c.val*P.L.val)(K:Sponsor G)(Q:Seasons K) (hm:Mag i j)(b u:ℝ)(V: Alps K Q i u)(he:V.gear=P.wing)(X:Medal P.patch G K.K i):
     let S:=P.visit (c:=c) (f:=f) K.K h; let T:=forest S.ratio P.odd; let U:Boxes G P.patch K.K:=⟨i,hm.1,X,V.gear⟩; let A: Matrix (Body 1 f) (Body 1 c) ℝ:= installed S.ratio (P.duo K.K.penalty).A0
     let H:= Prog K.K V.gear G f; let Mf:= Master (G:=G) S P.odd (P.duo K.K.penalty).A0; let m:=Chart.tangent G T.Free
     ∀ g : Bid.Dir G c→AxisChart G T, ∀ t:S.Choices, licensed S P.odd U V.clip V.live A V.sky g→ ∀ Y:Rill.FibreRep S P.odd U t (i:=i) V g b, ∀ p: Song (Vec G f 1), p∈ harmon (Vec G f 1) d → (∀ j:ℕ,Reserve H (p j)) → ∀ x: Bid.Dir G c,
       Y.L.Q.average m (fun y=>Strike d (CurlV (PhV K.K V.gear G f) d p) (flats G f (ribz S P.odd (Fiber.drape (Libra.Keys G (Body 1 c)) (Libra.Keys G T.Free) Y.L.M (x,y)))))= Strike d (CurlV (PhV K.K P.land G c) d (pulling Mf p)) (flats G c x):=by
          intro S T U A H Mf m g t hl Y p hx hy x; let W:= vertD (G:=G) S P.odd; let I:= FreeResolvent.insertion (plant T (G:=G)); let N:=H *(PhV K.K V.gear G f)
          rw [show (fun y=>Strike _ _ (flats G f (ribz S P.odd (Fiber.drape (Libra.Keys G (Body 1 c)) (Libra.Keys G T.Free) Y.L.M (x,y)))))= fun y=>Strike d (CurlV (PhV K.K V.gear G f) d p) (Mf*ᵥ flats G c x + W y) from ?_] -- evars
          swap
          · funext i
            erw [uprush S P.odd (P.duo K.K.penalty).A0 g V U t hl Y]
          refine sprouted m Y.L.Q W p (flats G c x) hx hy (Z:=N) ?_ ?_ (fun x y hp hv=>?_)
          · intro x y hh; unfold N; rw [← Matrix.mulVec_mulVec, dotProduct_comm, invertG _ _ (alignZ K.K V.gear G hm.1), hh, dotProduct_zero]
          · intro x hh; rw [← Matrix.mulVec_mulVec]; exact HealthN hm.1 V.gear x hh
          let J:=FUND S P.odd U; have hh: J= treeMatrix G S T (pink K.K.penalty P.wing):= by change treeMatrix G S T (pink K.K.penalty V.gear)= _; rw [he]
          change x ⬝ᵥ _=_ + x ⬝ᵥ (chamber Y.L.Q W *ᵥy); rw [show chamber _ W=I*J⁻¹* Iᵀ from fortune ..,hh,← mulVec_mulVec,← mulVec_mulVec,entrusted I]
          have hz:= rollingK (S:=S) (V:=T) (A:=(P.duo K.K.penalty).A0) (u:=P.land) (v:=P.wing) (P.tangent K.K hm.2.1 (c:=c) (f:=f) h).1 x y (show Health _ x from he ▸ hp) (show Health _ y from he ▸ hv) hm.1 hm.2.1 (hh ▸ ulk_force S P.odd U)
          rw [he]; exact hz
end YM.OPE.Cascade.Paver
