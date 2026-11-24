import YM.FormalBulk08.Spruce.Quota
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spruce
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X:Type}{E m n l e r j t d D R:ℕ}{F:Frame G d}{T:SectionData F}{W:Lab G K X}{H:Hol G}
variable {ρ:ChartRatio G}{o: Loc G 1}{Y Z:X→ Anthem D G}{g:X→ ℝ}{θ:ℝ}
variable (l ρ)(q:Quota F H W o D E R)(u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(C P Q:Pin W.scrolls)(hp:∀ i,C.N i≤ P.N i)(hz:∀ i,P.N i≤Q.N i)(hl:l≤R)(hR:d≤ R)
-- raw unprojections

def turf (x:Turn C)(Y:X→ Anthem D G): Anthem D G:= ledge D ρ W x.a (P.N x.a) x.b d l a (wave (T:=T) l ρ q a C P x.ups Y)
def feed (x:Turn C)(Y:X→ Anthem D G): Matrix (Letter F) Unit Pence:= pantry F (fun _:Unit=> turf (T:=T) l ρ q a C P x Y)
variable {ρ l}
    (hg:∀ i,0≤ g i)(hy:∀ i,Clef o (Y i) l)(hx:∀ i,Clef o (Z i) l)
    (hw:∀ e≤ E,∀ r,Brass ((sage C).reach (peak C)) o (fun i=> W.eagle (peak C i)) (hill C P hp) g (fun x p=> Y x p e r) (fun x p=> Z x p e r))
variable {X':Type}{τ:Time X'}{δ k:X'→ℝ}
structure Calm (τ:Time X')(δ k:X'→ℝ)(P Q:X'→ℝ): Prop where
    aF:Faint τ k P
    bF:Faint τ k Q
    diff:Faint τ (fun i=>δ i*k i) (fun i=> P i-Q i)
include u h hs ht hb hz hp hl hR hy hx hw hg
lemma timesheet (p:θ<1/2)(h':θ≤ 1):
    let t(i:Turn C):=g i.a*Dove.bump θ i
    ∀ e≤ E,∀ r,Brass (Dove.tide C) o W.sail (fun i=>hill C P hp i.a) t (fun i v=>turf (T:=T) l ρ q a C P i Y v e r) (fun i v=>turf (T:=T) l ρ q a C Q i Z v e r):= by
   intro t; obtain ht:=wintry q u h a hs ht hb C P Q hp hz hl hR hg hy hx hw p h'; have H i:0≤t i:= mul_nonneg (hg _) (ratioR_pos ..).le; have Hv e (h:e≤ E) r:= brass_fold_gen Turn.ups (up_age C u.liable) (ht e h r)
   intro e he r
   unfold turf ledge; exact full_income (F:=W.liftF) (V:=W.liftU) (H:=W.liftH) (T:=fun i=>wave (T:=T) l ρ q a C P i.ups Y) (S:=fun i=>wave (T:=T) l ρ q a C Q i.ups Z) (budge C P Q hp hz u h a hs) H (scooped C) d l e r he (fun j m hx=>Hv j (by unfold precede at *;omega) m) (Hv e he r)
lemma uses_fee (p:θ <1/2)(h':θ≤ 1)(i:Letter F)(he:e≤ E): Calm (Dove.tide C) (fun i=> hill C P hp i.a) (fun i=>g i.a*Dove.bump θ i) (fun j=>coeff e (feed (T:=T) l ρ q a C P j Y i ())) (fun j=> coeff e (feed (T:=T) l ρ q a C Q j Z i ())):= by
    let T' j:=turf (T:=T) l ρ q a C P j Y; let U' j:=turf (T:=T) l ρ q a C Q j Z
    have Ht:=timesheet q u h a hs ht hb C P Q hp hz hl hR hg hy hx hw p h'; obtain H':=payroll_from C q u P.N
    have hv i := u.zero (i:Turn C).toLeaf; have hK i (h:i≤ d):= H'.uptake i (by omega)
    refine ⟨reading (Y:=T') hv hK (fun j h r=>(Ht j h r).1) i he,reading (Y:=U') hv hK (fun j h r=>(Ht j h r).2) i he,?_⟩; have hQ:=reading (Y:=fun i=> T' i-U' i) hv hK (fun j h r=>brass_crisp (Ht j h r)) i he
    obtain hV:=confidential q u h a hs ht hb C P hp hy (tender_qual hg fun j he r=>(hw j he r).1); obtain hY:=confidential q u h a hs ht hb C Q (fun i=>(hp i).trans (hz i)) hx (tender_qual hg fun j he r=> (hw j he r).2); obtain Hc:=budge C P Q hp hz u h a hs
    apply hQ.lower; intro z
    have hv' :Wade o (T' z) l:=(migrate_w (P:=graded W.liftF (W.trail P.N) z) (V:=W.liftU z) a _ _ d (hV z.ups).1 (Hc.aV z) (Hc.church z) h le_rfl).fare
    have ht' : Wade o (U' z) l:=(migrate_w (P:=graded W.liftF (W.trail Q.N) z) (V:=W.liftU z) a _ _ d (hY z.ups).1 (Hc.bV z) (Hc.church z) h le_rfl).fare
    change |coeff e (echo F (T' z) i)-coeff e (echo F (U' z) i)|≤_ ; rw [chalk_less _ _ ht' hv',map_sub]
end YM.FormalBulk08.Spruce
