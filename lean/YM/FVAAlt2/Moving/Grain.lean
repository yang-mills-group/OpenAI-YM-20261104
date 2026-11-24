import YM.FVAAlt2.Moving.Port
/-! # Film encoding arbitrary profile arrays, compact uniform error along any requested mesh survey. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Moving.Pegs
open Function Set Filter MeasureTheory Real Topology
open Lattice Precision RG PhysicalNext.Repeat.Legato Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping Period.Field Sound CalendarT
open MS MS.Land MS.Dial MS.Rake MS.Vista MS.Fleet MS.Orbit MS.Tone MS.Tide
open PowerSeries Integration RunFormalChain FormalOPE Pipeline Pipeline.See Figure
open YM.FVAAlt2 YM.FVAAlt2.Home.Profiles
open scoped Topology ENNReal NNReal BigOperators PowerSeries Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(hG:G.Simple) {K:KernelChoices}{X:Type}
variable (Y:Oracle.Program K)(Z:∀ B:Patch,B.Branches K G)(C:Run G)(R:Lodge.Contract C Y Z)(t:X→ℕ)(ht:∀ x,R.floor Y Z C ≤ t x)
local notation "B"=> (R.profile Y Z C t ht)
local notation "P"=> ( Period.Field.LodgeT.instance_real Y Z C R t ht )
local notation "Γ"=> C.family.path
set_option quotPrecheck false
variable (F:Calibration.Tent ( ( R.profile Y Z C t ht ).entire )){g:G.ColorIndex} (p d:ℕ)
variable {n:ℕ}{u:MS.Local.Physical.Deck G}(D:Fin n→ MS.Rake.Label u)(T:MS.Land.Prescription u){J:Booked u}(H: MS_Data G J) (μ:ℝ)
variable (Λ:X→ℕ)(a:X→ Cover) -- center.Scale independent
open Extraction
abbrev Motor (B₁ : Lodge.Track X) (n:ℕ)(i:X):= CalendarT.nativeT B₁ i n
local notation:max "η" k:max=> (Sound.Alone (B) k)
local notation:max "θ" k:max=> (μ-(B).Θ k)
abbrev grain (w:X)(q:Motor B n w): PowerSeries ℂ:= Figure.runPer C Z P (fun _ j=> a w+ Lattice.lift (q j)) ( Calibration.sheet F ) (Λ w) ( B ).stop D T θ w η w w
local notation:max "W" i:max y:max=> (grain Y Z C R t ht F D T μ Λ a i y)
variable {E:Set (Points n)}(hE:IsCompact E) (hC:E⊆ conf n)
-- Abstract worst-film schedule, pick outputs only on valid offsets.It covers all such quantities simultaneous.F.Pin pixels apply for any single H test.Area.J.Storage.View. 
def Error (j:ℕ) (w:X)(q:Motor B n w) := ‖PowerSeries.coeff j ( W w q ) - Dial.tour H D μ (realize ( CalendarT.sample w q ) ) Finset.univ j‖
local notation "Err"=> Error Y Z C R t ht F D T H μ Λ a
private lemma aligned (x:X)(v:Motor ( B ) n x)(b: Fin n→ X→ Cover) (h:∀ j,b j x=Lattice.lift (v j)) (j:ℕ) : let c:= ( B ).PoseT μ a b; Err j x v= ‖(Sound.prospect Y Z C R t ht F D T μ Λ a b j x)- Dial.tour H D μ ( testP c x ) Finset.univ j‖:= by
   intro c; have ht': realize ( CalendarT.sample x v )= testP c x:= by rw [realize_t]; ext1 i; change _= (Alone _ x) • Tone.embed (b i x); rw [h]
   unfold Error Sound.prospect; rw [ht']; exact congr_arg (fun y:ℂ=> ‖y -_‖) (Sound.Ethos.holdings C Z P F T ( B ).stop (fun i=> θ i) (fun i=> η i) (Λ x) (fun _ j=> a x+ Lattice.lift (v j)) (Rocket.Zpose ( ( B ).PoseT μ a b )) x (funext fun i=> congr_arg (fun z=>a x+z) (h i).symm) D j)
variable (l:Filter X)(hV:Tendsto t l atTop)(hF: Notebook (R.profile Y Z C t ht).desk Y G Z g (Rocket.native _) F p)(hver:( R.profile Y Z C t ht ).VenueT a)(Hq:∀ x,p≤t x)(hT:TaylorOKPl H (Lobby.Table (basisR C) u) T)
variable {σ: X→ℕ}(hσ:Sound.Margin (I:=Fin n) Y Z C R t ht F p d T μ σ)(hv:∀ᶠ x in l,σ x ≤ Λ x) (hd:∀ i,( D i ).h≤d)
include hG hV hF Hq hver hT hC hE hσ hv hd
lemma uniform (j:ℕ)(hj:j≤p): ∃ C₀:ℝ,0<C₀ ∧ ∀ᶠ i in l,∀ q:Motor (B) n i, CalendarT.sample i q∈ E → Err j i q ≤ C₀ * Sound.BudgetAir (B) i:= by
 let A (i:X):= Finset.univ.filter (fun u: Motor B n i=> CalendarT.sample i u∈ E )
 let Z₁(i:X)(q:Motor (B) n i):= Err j i q
 have hs(x) (h:(A x).Nonempty):= (A x).exists_max_image (Z₁ x) h
 choose! y hh hh' using hs
 -- choose! maybe function y depends x only OK
 let v(k:Fin n)(x:X): Cover:= if (A x).Nonempty then Lattice.lift (y x k) else CalendarT.fallback (B) k x
 have he(x) (h:(A x).Nonempty)(i:Fin n): v i x=Lattice.lift ( y x i ):= if_pos h
 let c:=(B).PoseT μ a v
 have hw:∀ i:X,testP ( ( B ).PoseT μ a v ) i∈ realize '' E ∨ testP ( (B).PoseT μ a v ) i=CalendarT.sampleE:=by
   intro i; by_cases hx:(A i).Nonempty; swap
   · right; rw [show testP ((B).PoseT μ a v) i= _ from (show testP _ i=testP ((B).PoseT μ a (CalendarT.fallback (B))) i from ?_)]; swap
     · ext1 j; exact congr_arg (fun z:Cover=> (δ (B) i) • Tone.embed z ) (if_neg hx : v j i= _)
     exact CalendarT.discount ..
   left; refine ⟨ CalendarT.sample i ( y i ),( Finset.mem_filter.mp (hh i hx)).2,?_ ⟩; rw [ realize_t ]; ext1 j; change _= (Sound.Alone _ i) • Tone.embed ( v _ i ); rw [he i hx]
 obtain ⟨hm,hM⟩:= CalendarT.realistically (f:=v) (μ:=μ) a hE hC hw
 obtain ⟨ -,c₀,hx,hP ⟩:= Sound.finalT hG Y Z C R t ht F p d D T H l μ Λ a v hF Hq hV hver hm hM hσ hv hd hT j hj
 refine ⟨_,hx,hP.mono fun i hi u hu=>?_⟩
 have ht'(w:Motor _ n i): CalendarT.sample i w∈ E→ w∈ A i:= fun g=> Finset.mem_filter.mpr ⟨ Finset.mem_univ _,g⟩
 have hp:(A i).Nonempty:=⟨u,ht' u hu⟩
 exact le_trans (hh' i hp u (ht' u hu)) ((aligned Y Z _ R t ht F D T _ μ Λ a i _ v ( he i hp ) j ).le.trans hi)
end YM.RegulatorIR.FVAAlt2.Moving.Pegs
