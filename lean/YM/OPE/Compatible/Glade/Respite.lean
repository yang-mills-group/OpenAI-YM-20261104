import YM.OPE.Compatible.Glade.Tug
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {W:Type}{v b:W→ℝ}
-- regular voyages, auxiliary mobility.Link.
variable {x:ℝ}{X: Seasons K}
-- launch.Seam billing in Φ before reflections and Energy embedding.
variable {u v w:W→ℝ}{U:(i:W)→Boxes G P K.K}{A:∀ x:W,Alps K X i (u x)}{D:∀ x:W,Alps K X j (v x)}{n':W→Side}
-- local Transport start witness.
section voyages
variable (p':W→TileC X P p R x) (B: Medal P G K.K P.J) (hr:LocalRatio R)
abbrev keel :Rise (fun i=>UA (p' i)) (fun i=> UA (fallsF (p' i))) (fun i=>charmSeal B (UA (p' i)).gear) R (fun i=> betaA (p' i)):= ⟨fun _=>cuplet hr B _⟩
lemma Temp (v':ℝ)(hp:∀ i,upperX (p' i) ≤ v')(ht:Crest G P K.K m)(he:k+44 ≤ m)(hs:G.Simple): (keel p' B hr).Hiked k R:=by
    obtain ⟨a,b,ha,hb,H⟩:= Runic p' v' hp B ht; obtain ⟨c,hc,F⟩:= Verve (k:=k) p' v' hp B ht he hs hr; refine ⟨⟨a,b,c,ha,hb,hc,fun i=> ⟨H i,(F i).1,(F i).2⟩⟩,⟨x,fun i=>(p' i).1.1.bound _⟩,?_⟩; exact ⟨⟨p,fun i=> (p' i).1.1.R _⟩,⟨max 0 v',le_max_left ..,fun i=> le_trans (le_max_left ..) (le_trans (hp i) (le_max_right ..))⟩,fun i=> zero_le_one.trans (p' i).1.1.fits⟩
lemma VarB (v':ℝ)(h: ∀ i,upperX (p' i)≤ v')(ht:Crest G P K.K m)(he:∀ i,τ i ≤ m)(hh:Aware d τ)(hs:G.Simple): ∃ z:ℝ,∀ i:W, ‖(keel p' B hr).chant hs hr hh i‖ ≤ z:=by
       obtain ⟨a,ha,r,H'⟩:=(affordZ (p:=p) (b:=x) (T:=X) B hr hs ht hh 0 he).A; refine ⟨a*v'^r,fun i=>?_⟩; have he: ‖(keel p' B hr).chant hs hr hh i‖ ≤ a*upperX (p' i)^r*1:= H' (p' i); rw [mul_one] at he; exact he.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (max_cap (H:=X) (P:=P) (p:=p) (V:=R) (C:=x) _)) (h i) r) ha)
end voyages
section alone
variable {A'' D' u':ℝ}{T:Seasons K}{A':Alps K T i A''}{D:Alps K T j D'}{U:Boxes G P K.K}
theorem Visite (h:Town A' D U R u')(W:Type): Rise (fun _:W=>A') (fun _=>D) (fun _=>U) R (fun _=>u'):= ⟨fun _=>h⟩
lemma temp' (t:Town A' D U R u')(h:0 ≤ D')(k:ℕ)(W:Type): (Visite t W).Hiked k R:=by
     obtain ⟨a,b,ha,hb,H⟩:= spineP P K.K U; obtain ⟨c,hc,F⟩:=gaV P K.K A' R 0 (k+44); have he := (U.folk_fly A'.pays)
     have hv(i):folk (voteV P K.K A'.live A'.clip i):= folkS (penne_unit _ _ _ _ A'.pays _) _; obtain ⟨z,hz⟩:=hv 3 (k+24); obtain ⟨x,hx⟩:=hv 4 (k+24); obtain ⟨y,hy⟩:=he (k+24); let m:=max c (max z (max x y)); refine ⟨⟨a,b,m,ha,hb,hc.trans (le_max_left ..),fun i=> ⟨⟨H.1,H.2.1,H.2.2.1,H.2.2.2⟩,fun i=> (F i).tips (le_max_left ..),hz.tips (by unfold m;grind),hx.tips (by unfold m;grind),hy.tips (by unfold m;grind)⟩⟩, ⟨|u'|,fun _=> le_rfl⟩,⟨⟨D.clip,fun _=> rfl⟩,⟨D',h,fun _=> le_rfl⟩,fun _=>h⟩⟩
end alone
end YM.OPE.Quit.PriceZ
