import YM.FormalOPE.RG10.Boardwalk.Score
/-!
 # Finite Frame receipt and its inverse when ready at reported clock

At SAME F basis and Roll widths. Computing with `Mark` after choosing all gauges & fits at
κ.Open events. This is the A-report normalized Peal transformation to eventually use expressed
in forecast variable $g_k$, given relation to those raw stencil-and-positioned arrays by a producer.
Need `Fanfare`'s exact real-oriented atlas tests, etc. No claims of `A_X` conversion to actual
(or any independent continuum subtraction convention) from this polynomial. The customer uses
both `converse` and orientation upright lemma here before a projection on forms. No assertions
of ranks on ambient actual phase fields with gauge factors. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk.Stagecraft
open Filter Function Finset PowerSeries Clearing Ledger Rates InversionTop
open Carryon PertExtension Position Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric PertExtension.Position Triangle Lawn
open RG10.Profile Gliss Gazebo Matrix Position.Grade Peal Trellis Fanfare
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge}{F:Frames G}{I:Type*}{l:Filter I}{P:Path l}{r d:ℕ}
variable (R:Position.Grade.Rails F)
variable {D:Stock F}
local notation "Ψ" d=>Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "κ" d=>Deck F d
local notation "Κ" d=>Matrix (Deck F d) (Deck F d) fps
local notation "ins" d=>PertExtension.Position.insert (Deck F d) PertExtension.Physical.Profile.n

def rotation (D:Stock F)(x:Mark (Deck F d) PertExtension.Physical.Profile.n→fps) (w:Warp) := ((R.book d).map w.charge)* Carryon.posture D x
lemma framing (D:Stock F)(x:Mark (Deck F d) PertExtension.Physical.Profile.n→fps)(f:(Ψ 6)→ fps) : adjusted D R f x = (ins d) x (rotation R D x (peal D f)) := insert_twice ..

-- remains in tents. exponents & first row.
lemma mainBook : Upright (R.book d):= by
 refine Carryon.Upright.obtainable _ ?_ fun i hi=> ?_
 · rw [show Stg (R.book d) 0=1 from (R.route d).first_base]; rw [sub_self]; exact (tents F d).zero_mem
 apply pinned .. |>.mpr; refine ⟨(votes _).mpr ⟨fun u v h=> by -- cost ordering
   simp only [of_apply,Stg]; exact (congr_arg (coeff i) ((R.route d).booked.1 _ _ h)).trans (map_zero _),?_ ⟩,?_⟩
 · intro s; ext1 u v; have ht:=congr_arg (coeff i) (congr_fun₂ (R.preserves s d) u v)
   simp only [Matrix.mul_apply, _root_.map_sum, Matrix.map_apply,coeff_C_mul,coeff_mul_C, Matrix.of_apply] at *; exact ht
 funext v; change coeff i ((R.book d) (Deck.start F d) v) = (0:ℝ); rw [R.leaves_unit,Matrix.one_apply]; split; simp [hi.ne']; simp

lemma meaning (h: Official D)(x:(Ψ d)→ fps)(f:Warp): Upright (rotation R D x f):= (Carryon.Warp.worth _ f (mainBook R)).mul (installed _ h)

variable {x y:I→ Mark (Deck F d) PertExtension.Physical.Profile.n→fps}
variable {f g:I→ Mark (Deck F 6) PertExtension.Physical.Profile.n→fps}
variable {L:I→Matrix (Deck F d) (Deck F d) fps}{U:I→Matrix (Deck F 6) (Deck F 6) fps}
variable (B:Fanfare P D r x y L) (W : Fanfare P D r f g U) (h:Polls P r f g U)
local notation "b" i=> peal D (g i)
local notation "A₀" i=>rotation R D (y i) (b i)
include B
lemma moveOn : listens (l:=l) (D:=D) y:=
 let he := Alert.uptake B.heartbeat B.breach
 (testVector (D:=D d) B.alert).both (raw F d ∘ markIn _) he
lemma step : Acr P (fun i=>constantCoeff (A₀ i).det):= by
 apply Bars.obligate (F:=fun i=> A₀ i) (by simp : IsUnit (1:Matrix (Deck F d) (Deck F d) ℝ).det)
 have he v : ((rotation R D (y v) (peal D (g v))).map constantCoeff)= Stg (Carryon.posture D (y v)) 0 := by
   unfold rotation; rw [Matrix.map_mul]; have h0 : ((R.book d).map (peal D (g v)).charge).map constantCoeff=1:= by
        have h':= Warp.look (R.book d) (peal D (g v)); change Stg _ _=_ at h'; rw [show ((R.book d).map ((peal D (g v)).charge)).map constantCoeff=_ from (show _=Stg ((R.book d).map (peal D (g v)).charge) 0 from (canvas _).symm), h']; exact (R.route d).first_base
   rw [h0,one_mul]; exact (canvas _).symm
 simp_rw [he]; exact start_up B.standard _ (moveOn B)
include W h
local notation "Ξ"=> fun i=> A₀ i
lemma allocated : Bars P r (fun i=>rotation R D (y i) (peal D (g i))) (fun i=> rotation R D (y i) (peal D (g i))):= by
 refine Bars.mul ?_ ?_; -- unfolds automatically?
 · intro a c; exact Posi.century (Posi.fixed ((R.book d) a c)) (Posi.same ((W.fares h).rights))
 intro a c; exact Posi.same ((Gliss.posture (D:=D d) (B.standard.fresh d) (Alert.uptake B.heartbeat B.breach) B.alert a c).rights)
lemma converse : Bars P r (fun i=>(rotation R D (y i) (peal D (g i)))⁻¹) (fun i=>(rotation R D (y i) (peal D (g i)))⁻¹) := Bars.leasing (allocated R B W h) (step R B)
end YM.FormalOPE.RG10.Boardwalk.Stagecraft
