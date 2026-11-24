import YM.OPE.Compatible.Glade.Nits
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
abbrev χ' (n:Side) (P:Patch)(K:Sponsor G):= (subStud P K.K n).ratio -- K not section used revise
structure Rise (A:∀ x:W,Alps K X i (u x))(D:∀ x:W,Alps K X j (v x))(U:(i:W)→Boxes G P K.K)(R:ChartRatio G) (z:W→ℝ) where
    fee (x:W): Town (A x) (D x) (U x) R (z x)
namespace Rise
variable (Y:Rise A D U R w)
local notation "L!"=>solar G d τ
variable (h:∀ i,Even (n' i).val)(hx:∀ i,barrier P≤ (n' i).val)(hi:4 ≤ i)(hj:4 ≤ j)(hS:G.Simple)
noncomputable def go' (i:W):= genS (Y.fee i) (h i) (hx i) hi hj hS
variable (hr:LocalRatio R) (Kq:Aware d τ)
abbrev chant (i:W):= actor (A i) (U i) R 0 (RollD.mk hS hr (Y.fee i).eph) Kq
abbrev spireX (i:W):= yankV (D i) (Y.fee i) hr hS Kq
-- budgets.
structure Hiked (Y:Rise A D U R w)(k:ℕ)(R':ChartRatio G) :Prop where
 pin :∃ a b c:ℝ,0<a ∧ 0 ≤ b∧ 1 ≤ c∧∀ i:W,Telet P (U i) a b ∧
    weightsB (novel P K.K (u i) _ (A i) 0 R') (k+44) (fun _=>c)∧ soot (k+24) (voteV P K.K (A i).live (A i).clip 3) c ∧ soot (k+24) (voteV P K.K (A i).live (A i).clip 4) c ∧ soot (k+24) ((U i).Fly (A i).live (A i).clip) c
      -- R' avoid filler theorem.
 fare :∃ z, PathL z w
 out :Foam D
include hx h Kq
local notation "Lσ" i=> χ' (K:=K) (n' i) P
lemma rubbing (hv:Y.Hiked k R)(hp:∃ z:ℝ,∀ i,‖Y.chant hS hr Kq i‖≤z)(p q:W→ L!)(a b:(i:W)→ Site (n' i))(z:ℝ)(hz:2 ≤ z)(hs:∀ i,Settle (a i) (b i) z)(hh:∀ i,k+44 ≤ τ i)(Q:∀ i, Plot (h i))(V:∀ i,Plot (even_both (Lσ i) (h i))):
    let Φ(i):= SpecH (A i) (even_both (Lσ i) (h i)) hi hS (V i) (p i) (q i) ((Lσ i).embed (a i)) ((Lσ i).embed (b i)) R
    let t(x:W→L!)(i:W):= (Y.spireX hS hr Kq i) (x i)
    let P(i):= SpecH (D i) (h i) hj hS (Q i) (t p i) (t q i) (a i) (b i) R
    Permit n' (Scape.Setup G d) (Scape.passM p*Scape.passM q*Scape.gDump n' k) (Φ-P):=by
       intro f t g
       let L(i:W):= genS (Y.fee i) (h i) (hx i) hi hj hS
       obtain ⟨a',y,c,h₁,h₂,hc,F⟩:= hv.pin; obtain ⟨g',hg',H⟩:= hv.out.cap; obtain ⟨c',hφ⟩:= hv.out.coast; obtain ⟨cost,hx'⟩:=hv.fare; obtain ⟨T,Hv⟩:=hp
       have hr' : Scape.Rebate L cost g' c':= ⟨hx',hg',hv.out.bill,H,hφ⟩; have he:Scape.SlopePrice L k a' y c:=⟨h₁,h₂,fun i=>(F i).1,hc, fun i=> (F i).2.1, fun i=> (F i).2.2⟩
       let Q'(i):= (L i).E
       rw [show g=(fun i=>let x:=L i; RGram (h i) x.E x.V (x.upL hS hr Kq (p i)) (x.upL hS hr Kq (q i)) (a i) (b i) R) from funext fun i=>?_]; swap
       · have heq:= parade (h i) (Q i) (bredV (D i) 0 _ hj hS) (t p i) (t q i) (a i) (b i) (Q' i) hr; exact heq.trans (topD' (Y.fee i) (h i) (hx i) hi hj hS (p i) (q i) (a i) (b i) Kq hr)
       exact Scape.SeamBill L hS hr he hr' Kq hh hj p q a b T (fun i=>Hv i) z hz hs (fun i=> show Bor (even_both (L i).rungS.ratio (h i)) (A i) 0 from bredV _ 0 _ hi hS) V Q'
end Rise
lemma hushP {z p:W→ℝ}(hh: Cash n' e (p*Scape.gDump n' (e+k)) z) :Cash n' 0 (p*Scape.gDump n' k) z:=by
    obtain ⟨a,ha,H⟩:=hh; refine ⟨a,ha,fun i=>(H i).trans_eq ?_⟩; rw [Pi.mul_apply,Pi.mul_apply]; unfold Scape.gDump; rw [pow_zero,mul_one,pow_add,inv_pow]; have hp : (n' i).val≠0:= (n' i).pos.ne'; field_simp
end YM.OPE.Quit.PriceZ
