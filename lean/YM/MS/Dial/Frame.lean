import YM.MS.Dial.Paint
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
variable [LinearOrder W] {B:Deck G}{M:Booked B}{b:MS_Data G M}(X:W→Label B){x:Position W I}{K:Rake.Dance G I W}
local notation "m0"=> (fun (_:I)=>planeF)
local notation "Sκ"=> approach (frameF I v) b
variable (h: Mesh (frameF I v) x)(ht:DOrd M (frameF I v) b X x K) {s:Finset W}{n:ℕ}
-- index copy.Frame general
open Train Dock
variable {P:Geo I}(q:Belt I)
lemma Architect (he:Gold P q): Arch q D D ( approach P b ) ( rowM P b ∘ X ) ( Label.h∘X ):= by
    have hx:= cost_D (G:=G) he.day; have hv(i:q.time) : ‖P.η i.1+tstart i‖ ≤ q.price.basic i:= ( norm_add_le .. ).trans (le_trans (b:=_) ?_ (he.quote i)); swap; · have hh:=he.paid i; unfold habitat; rw [norm_of_nonneg hh, norm_eq_abs ]; nlinarith [abs_nonneg (P.η i.1) ]
    exact ⟨ fun i j=> polar ( hx i j ), hx, fun n _=> nameD ( S:=q.price ) ( Emit.Host.host ( Dock.gang ( b.bulkOK n ))) he.day hv, fun i n=> nameD ( S:=q.price ) ( Emit.Host.host ( Dock.gang ( b.markOK ( X i |>.h ) ( X i |>.item ) n ))) he.day hv ⟩
-- result standard DOrd exists independent.P.R. Test.Stat.
lemma reports (h: Mesh P x)(ht:DOrd M P b X x K)(hp:s.Nonempty)(n:ℕ): Verdict P ( charge ( Label.h ∘ X ) s ) 0 ( K s n ):= Vane.closure ( builder b h X ) ( Architect X ( Gulf P ) gulfG ) ( Architect X ( West P ) westV ) ht hp n
open scoped Classical
variable {J:Type}{Q:Geo J}{U:Rake.Dance G I W}
def copy (i:J→I)(A:Rake.Dance G I W): Rake.Dance G J W:= fun k n=> A k n ∘ i
lemma basis_copy (K:Position W I)(u:J→I)(x:Finset W): rootX (fun w=>K w ∘ u) x=( rootX K x ) ∘ u := by
   unfold rootX; split <;> rfl
lemma valid_copy (hx:DOrd M P b X x U)(a:J→I)(he:∀ i, Q.η i=P.η ( a i )): DOrd M Q b X (fun i=> x i ∘ a ) ( copy a U ):= by
    unfold DOrd Fields; let V:= copy a U; refine ⟨ ?_,fun i=>?_,fun s h n=>?_⟩; · funext j i; change U ∅ j (a i)=_; rw [hx.1]; rfl
    · funext j p t; change U {i} j (a p) t=_; rw [hx.2.1 i ]; exact Eq.symm ( congr_arg (fun v=> Outlook.Archive ( X i|>.h ) (b.marks _ ( X i |>.item )) j (v,t)) ( he p ) )
    let S:= Src x m0 D D (approach P b) U s n; let F:= sailP m0 D (U s n)+S;
    let L : Planet G J:= constantP G J ( PlanetD G ); let T:= Src (fun i=>x i ∘ a) (fun _=>planeF) L L ( approach Q b ) V s n;
    have hh : ( sailP (fun _=>planeF) L ( V s n )+T )= F ∘ a:= by
       funext j t; dsimp only [ F,T,S, Src, multi, lonely, expJ, V, copy ]; simp only [ Pi.add_apply, comp_apply, Finset.sum_apply, basis_copy ]; refine congr_arg₂ ( ·+· ) rfl (congr_arg₂ (·+·) (Finset.sum_congr rfl (fun i hp=>?_)) ( Finset.sum_congr rfl (fun i hi=> Finset.sum_congr rfl (fun j _=>?_)))); · unfold approach circle nameR expJ; dsimp only; rw [he]; rfl
       rfl
    obtain ⟨⟨k,hK⟩,hS,hL⟩:= hx.2.2 s h n; change collect ( V s n ) ∧ Latch.Job.train false ( sailP _ L ( V s n )+T ) ∧ V s n= river (sailP _ L ( V s n )+T); rw [hh]; exact ⟨ ⟨ k,fun i t=> hK _ _ ⟩,fun i=>hS ( a i ), congr_arg (· ∘ a) hL ⟩ -- ξ complex.Apply
end YM.MS.Dial
