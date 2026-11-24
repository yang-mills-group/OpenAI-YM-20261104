import YM.MS.Dial.Time
/-!
# Negative time domination in continuum frame.Purpose: separated continuity; also grants actual PT regulator statements on sequences of profile samples converging to fixed physical positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Vane -- alias
open scoped Topology ContDiff
variable {I W E:Type} {G:Gauge} {v t:ℝ}{a b:ℤ}{l:Filter I} {r:ℕ}
set_option quotPrecheck false
local notation "Υ" => east ( frameF I v ) false
local notation "Ω"=> ( Υ ).price
open Wire Belt
variable {F H:Glade G I}{m:I→QP}
variable {p:I}
local notation "R"=> frameF I v
local notation "D"=> constantP G I (PlanetD G)
abbrev rhythm (F:Glade G I):= ∀ (s:ℝ),s ≤ 0→ ∀ w,tend l p (fun i=>F i s w ) -- l p invisible implicit please explicit
lemma power0 : Sheet Ω 1 (plug D):= ( masterD G I R ).well
lemma chew (hp:tend l p (m))(q:QP) : tend l p (fun i=> Tone.bill (m i) q):= by simp_rw [ Tone.rights (m _) q ]; exact ( Fiddle.sailor q|>.shore.continuousAt.tendsto ).comp hp
lemma shore {A:Type} (s:Sector A)(w:Legs A)(f:I→ Shared A ℂ)(hp:∀ a b,tend l p (fun i=> f i a b)): tend l p (fun i=> scatter s w (f i)):= by induction w generalizing f with| nil=> exact hp _ _| cons i w ih=> exact ih _ (fun a b=> (hp (i::a) b).add ((hp a (i::b)).const_mul _)) -- casts
variable [l.IsCountablyGenerated]
lemma joins0 (h:Here false true Υ F (rateS Υ a))(hx:Here false true Υ H ( rateS Υ b ))(ht:tend l p m)(hF: rhythm ( l:=l ) (p:=p) F)(hh:rhythm ( l:=l ) (p:=p) H) : rhythm (l:=l) (p:=p) (regionC (fun _=>planeF) m D F H):= by
    intro s hs w; unfold regionC Cabin; refine shore _ _ _ (fun A B=> Tendsto.mul (chew ht _) ?_); apply tendsto_finsetSum; intro i hi; apply tendsto_finsetSum; intro j hj; let f := packMesh i j (plug ( J:= (Υ).slot ) D) (plug F) (plug H) (ray A) (ray B); have hx0(t:I)(q:QP): meshZ ( D t s ) i j ( F t s ) ( H t s ) A B q= f ( slotL hs t ) (q,(1:ℝ)):= by unfold f packMesh plug; rw [ray_sail,ray_sail ]; rfl
    simp_rw [ hx0 ]; refine pole_pos hs (meshC (S:=Ω) ( power0 ) i j (add_split (ray A) (ray B)) h hx ) p (fun i=>?_) (fun i=> Fiddle.sailor (m i)) 1 (fun q=>?_); · rfl
    change tend l p (fun t=> Tone.bill (m t) q * f (slotL hs t) (q,1)); simp_rw [← hx0, meshZ]; exact Tendsto.mul (chew ht q) ( Tendsto.mul ( Tendsto.const_mul (2*( PlanetD G s ) i j q) ((hF s hs ((i,q)::A)).const_mul ((cross (parity j) (degree (field Landau.parity) A)):ℂ)) ) ( hh s hs (( j,-q )::B) ))
lemma loopT (ht:t≤0)(w:Legs (Lane4 G))(hp:Came R false F)(h:∀ x:Legs (Lane4 G), w.length < x.length → tend l p (fun i=> F i t x)): tend l p (fun i=> Ccy ( PlanetD G t ) ( F i t ) planeF w ):= by
   let P:( Υ ).time→ QP×ℝ→ℂ:= fun i q=> trc ( D i.1 i.2 ) q.1 (plug ( J:=( Υ ).slot ) F i) (sail ( ray w ) q.2); let X:= ( 1: ( Υ ).time→ℝ ); have hc := topCycle ( Lease.highp (hp.1.pick 0) ) ( power0 (G:=G) ) ( ray_course (b:=false) (fun i=> Bool.noConfusion i ) ( w:=w ) ) ( ( born R G false ).1 0 ) ( fun i=> zero_le_one );
   have he (i:I)(q:QP): (1:ℂ)*P ( slotL ht i ) (q,1)=trc (PlanetD G t) q (F i t) w := by unfold P; rw [ one_mul,ray_sail ]; rfl
   unfold Ccy; simp_rw [ ← he ]; refine pole_pos ht hc p ( fun i=>rfl ) ( fun i=>?hpeak ) 1 ( fun i=>?_ ); swap; · change tend _ _ (fun i'=> (1:ℂ)* P _ _ ); simp_rw [he,at_trc]; exact tendsto_finsetSum _ (fun i _=>tendsto_finsetSum _ (fun j _=> (h _ (by simp) ).const_mul _))
   exact ⟨fun _=> norm_one (α:=ℂ)|>.le, continuous_const⟩
end YM.MS.Dial
