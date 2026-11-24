import YM.FVA2.Smooth.Ways
/-!
# DCT domination on MS `Mesh` patches (negative t representation)

Need the full power-count estimates already available on these kernels in the
supplied `YM/MS` formalization. Use at the `Smooth/Window` rung.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Smooth.Cruise
open Set Function Filter Finset Metric MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake
open MS.Breeze MS.Book MS.Book.Convolve MS.Plane.Flux MS.High MS.Rake.Geo MS.Vane MS.Vista MS.Motif MS.Plane.Wire
open MS.Tone.Frame MS.City MS.Osc MS.Osc.Snap Belt
open MS.Land MS.Local.Physical MS.Dial MS.Port
open Lifetime Slots
open Complex (I)
open scoped Topology ContDiff BigOperators Interval
variable {W I : Type}{G:Gauge}{P Q:Geo I}{b:Deck G}{M:Booked b}
variable {k:ℝ}
local notation "ℳ"=> (fun (_:I)=>planeF)
local notation "Δ"=> Rake.Geo.constantP G I (PlanetD G)
local notation "Ψ"=> (field (p:=Landau.parity ( A:=Axis ) (C:=G.ColorIndex) ) (P:=QP))

variable {v:ℝ}{r n:ℕ}
open MS.Tide
set_option quotPrecheck false
local notation "R"=> frameF I v
local notation "Υ"=> east R false
local notation "Ω"=> (Υ).price
variable {F H: Glade G I}
variable {s a b0:ℤ}{t:ℝ}
variable [Nonempty I] (p:I→QP)
open MS.Plane.Flux MS.Fiddle

lemma parallel (ht:t ≤ 0)(hf:Came R false F)(w:Legs ( Lane4 G )): Boxed planeF (fun i q=> trc (PlanetD G t) q ((relax p F) i t) w):= by
    let P:( Υ ).time→ QP×ℝ→ℂ:= fun i q=> trc ( Δ i.1 i.2 ) q.1 (plug ( J:=( Υ ).slot ) F i) (sail ( ray w ) q.2);
    -- Wire.sail? check, ray conflict Abroad.
    have hc := topCycle ( Lease.highp (hf.1.pick 0) ) ( Dial.power0 (G:=G) ) ( ray_course (b:=false) (fun i=> Bool.noConfusion i ) ( w:=w ) ) ( ( born R G false ).1 0 ) ( fun i=> zero_le_one );
    have he(i:I)(q:QP): trc (PlanetD G t) q (( relax p F ) i t) w= Tone.bill (p i) (net w)*P ( slotL ht i ) (q,1):= by unfold P; rw [ ray_sail ]; exact traced ..
    simp_rw [ he ]; have hv (i:I): Continuous (fun q:QP=> P (slotL ht i) (q,1)):= (hc.smooth ( slotL ht i )|>.continuous ).comp ( f:=fun q:QP=> (q,(1:ℝ)) ) (by fun_prop);
    obtain ⟨f,hF,h⟩:= major ht hc (Classical.arbitrary I) ( fun i=>rfl ) 1;
    refine ⟨ fun i=> (continuous_const.mul ( hv i ) ).aestronglyMeasurable, f, hF, Eventually.of_forall (fun q i=>?_)⟩; rw [ norm_mul,Tone.bill_norm,one_mul ]; exact h i q

lemma aboardM (m:I→QP)(ht:t≤0)(h:Here false true Υ F (rateS Υ a))(hx:Here false true Υ H ( rateS Υ b0 ))(i j:BH G)(A B:Legs (Lane4 G)): Boxed planeF (fun x q=> meshZ (PlanetD G t) i j ((relax p F) x t) ((relax m H ) x t) A B q):= by
    let f := packMesh i j (plug ( J:= (Υ).slot ) Δ) (plug F) (plug H) (ray A) (ray B);
    let k (x:I):= Tone.bill (p x) (net A)*Tone.bill (m x) (net B); let u(x:I):= (p-m) x;
    have hz:= meshC (S:=Ω) ( power0 ) i j (add_split (ray A) (ray B)) h hx;
    have he(x:I)(q:QP): meshZ (PlanetD G t) i j ((relax p F) x t) ((relax m H) x t) A B q = k x*(Tone.bill (u x) q *f (slotL ht x) (q,1)):= by
       unfold f packMesh; rw [ray_sail,ray_sail ]; exact mesh_t ..
    simp_rw [ he ]; have hv (x:I): Continuous (fun q:QP=> f (slotL ht x) (q,1)):= (hz.smooth ( slotL ht x )|>.continuous ).comp ( f:=fun q:QP=> (q,(1:ℝ)) ) (by fun_prop);
    obtain ⟨P,hP,h⟩:= major ht hz (Classical.arbitrary I) ( fun i=>rfl ) 1;
    refine ⟨ fun x=> (continuous_const.mul (( sailor (u x) |>.shore ).mul ( hv x )) ).aestronglyMeasurable, P, hP, Eventually.of_forall (fun q x=>?_)⟩; simp only [k,norm_mul,Tone.bill_norm,one_mul ]; exact h x q

omit [Nonempty I] in
lemma ancestor (ht:t≤0)(hv:Came R false F)(w:Legs (Lane4 G)): Boxed (volume.restrict (Set.Iic t)) (fun i q=> relax p F i q w):= by
    let M:= volume.restrict (Set.Iic t); have he : ∀ᵐ x:ℝ ∂M,x≤0:= (ae_restrict_mem measurableSet_Iic).mono fun _ h=> le_trans h ht;
    obtain ⟨f,hF,h⟩:= boxX _ hv w; refine ⟨ fun i=>?_,f, hF.mono_set (Iic_subset_Iic.mpr ht), he.mono fun x hx i=> le_trans ( (plate F p i x w).le ) (h i x hx)⟩; simp_rw [ cove ]; exact ( continuous_const.mul (hv.1.mood.walk i w (fun i=>Bool.noConfusion i)) ).aestronglyMeasurable

-- Folk came. Wake.source generalized.
variable (S:MS_Data G M) {x:Position W I} (u:W→Rake.Label b)(v': Steps W)[LinearOrder W]{V:Dance G I W}
local notation "Sκ"=> approach R S
-- this is anchored. bounds on all frames.Index.V. do not carry to positive t except travel.p 
omit [Nonempty I] in
lemma clocks (h: Mesh R x)(ht:charted R S u v' x V)(T:Finset W)(hs:2≤T.card)(n:ℕ) : Came R false (folk x V T n Sκ):= by
    let K:= toTour R S u v' x h; obtain hv:= Dial.CameZ (emerged K ht hs n); suffices he: Came R false (road (G:=G) x Sκ V T n) from ⟨ hv.1.add he.1, collect_p hv.2 he.2 ⟩;
    unfold road Src multi lonely; obtain hx: CabinF (K:=Υ) (birthTar R) (∑ i∈ Domain.paths n 0, expJ Δ ( Sκ (n-i) ) ( V T i )) ∧ collect (∑ i∈ Domain.paths n 0, expJ Δ ( Sκ (n-i) ) ( V T i ) ):= seamount ( fun i hi=> cone K.ground ( emerged K ht hs i ) ( K.energy ( n-i ) ( by obtain hv: i<n:= (Finset.mem_Ico.mp hi).2; omega ) ) );
    have he: Came R false (∑ i∈ picks T, ∑ j∈ antidiagonal n, regionC ℳ ( rootX x i - rootX x T ) Δ ( V i j.1 ) (V (T\i) j.2 )):= by
        apply seamount; intro i hi; apply seamount; intro j hj; obtain ⟨r,hr⟩:= tip0 K ht ( n_small hi |>.2.1 ) ( n:=j.1 ); obtain ⟨q,hq⟩:= tip0 K ht ( n_small hi |>.2.2.1 ) ( n:=j.2 ); exact Geo.touch K.ground ( Rake.space h hi ) hr hq
    exact ⟨ hx.1.add he.1, collect_p hx.2 he.2 ⟩
end YM.FVA2.Smooth.Cruise
