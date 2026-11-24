import YM.FormalBulk08.Vale.Ways
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Vale
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
/-! DK propagation port. -/
variable {K:KernelChoices}(P:Flight j t)(R:Lodge P.patch)(ρ:ChartRatio G)(W:Pot G)(h:P.patch.Branches K G)
variable (u:(n:Side)→(primary P.patch K n).Choices)(a:hue G)(o:edgeL G)(V:I→Pot G)(μ:I→ℕ)(L:List I)(hv:∀ i∈L,Ritual (V i) (μ i))(hP:Story W (pink K.penalty P.wing))(hs:LocalRatio ρ)(ht:4 ≤ t)
abbrev originP (G:Gauge) (P: Patch)(R:Lodge P)(x:edgeL G) := coastRight _ (Minor G P R) _ x
abbrev boardWake (T:Pot G):= border P R W T ρ h
def morsel := boardWake P R ρ W h (packV V L)- campfire (fun i=>boardWake P R ρ W h (V i)) L
lemma heathG : Sweep (lands (rayshot P R h)) (GaugeR P R h):= by
    obtain ⟨σ,C,hσ,H⟩:=(gamma_ready G K P R h).1; have hC:=strip_mono H le_rfl (le_max_right 0 C); refine ⟨?_,⟨σ,_,hσ,.of_forall (fun n=> ray_grated P R h hσ.le (le_max_left 0 _) hC n)⟩,ray_flip P R h⟩
    exact landing_row _ (Row.rights _ _ (rayStrip P R h (le_max_left 0 C) hC) hσ.le)
include hP hs ht
lemma verified_single (T:Pot G)(l:ℕ)(hQ:Ritual T l)(i e r): WavePath (originP G P.patch R (chief P o o.2)) (boardWake P R ρ W h T i e r) (fun n=> calendarQ P R W T ρ h l n (u n) i e r):= by
    obtain ⟨σ,hσ,hG⟩:= pledge hQ o e; obtain ⟨w,hw,H⟩:= demanded_finite P W hP e;obtain ⟨s,C,hs',hC,hA⟩:=aone P (K:=K) G ht; obtain ⟨z,B,hz,hB⟩:=(gamma_ready G K P R h).1; let k:=min σ w;have hk:0<k:=lt_min hσ hw; let v:=min (min s z) (P.L.val*k); have hq:0<v:=by unfold v;positivity
    exact ⟨v,hq,budding P R W T ρ h hP hs hQ.young hQ.committees le_rfl u i e r hq hC (strip_mono hA ((min_le_left ..).trans (min_le_left ..)) le_rfl) (show v ≤ P.L.val * k from min_le_right ..) (le_max_left 0 B) (strip_mono hB ((min_le_left ..).trans (min_le_right ..)) (le_max_right ..)) o o.2 (fun a ha b=>⟨_,(H _ ha b).choose_spec.shrink (min_le_right ..)⟩) (fun a ha b=>⟨_,penn_shrink (hG a b ha).choose_spec (min_le_left ..)⟩)⟩
include a hv
lemma pathE (i e r): WavePath (originP G P.patch R (chief P o o.2)) (morsel P R ρ W h V L i e r) (fun n=> Lava.posting (tectonic P R ρ W h n (u n) V μ L) i e r):=by
    simp_rw [printed] -- remove P i e
    exact (verified_single P R ρ W h u o hP hs ht _ _ (orchestra V μ L hv a) i e r).dust (cuffs L (fun i hi=> verified_single P R ρ W h u o hP hs ht _ _ (hv i hi)) i e r)
lemma comprise : let D:= morsel P R ρ W h V L
                   let q:= lands (rayshot P R h)
                   D 0=0 ∧ ∀ i e r, D (i+1) e r=((i+1:ℕ):ℝ)⁻¹ • (stare q (D i e (r+1+1))+(2:ℝ) • brawl q (magma P R W ρ h) D i e r+(2:ℝ) • collision q (fun b=>boardWake P R ρ W h (V b)) L i e r):=by
    intro D q; let o:edgeL G:=(0,Exterior.coord 0,a); let u(n:Side):=(Classical.choice (chooseable n (n*P.patch.L) (primary P.patch K n)))
    have hr n:=rumble P R ρ W h n (u n) a V μ L hv hP hs ht; let T n:= Lava.posting (tectonic P R ρ W h n (u n) V μ L)
    have H n : T n 0=0:= (hr n).2.1
    let A:= originP G P.patch R (chief P o o.2); have hp :∀ i e r, WavePath A (D i e r) (fun n=> T n i e r):=pathE P R ρ W h u a o V μ L hv hP hs ht
    constructor
    · funext e r; specialize hp 0 e r; simp_rw [H] at hp; exact hp.agree (wave_empty ..)
    intro i e r; apply (hp (i+1) e r).agree; simp_rw [show ∀ n:Side,T n (i+1) e r=_ from fun n=>(hr n).2.2 i e r]; have hA:=heathG P R h
    refine (((grazed hA (hp i e (r+1+1))).plus ((path_jost hA ?_ hp i e r).money _)).plus ((waveCollision hA L (fun z hz=> verified_single P R ρ W h u o hP hs ht _ _ (hv z hz)) i e r).money _)).money _
    intro i e r he; exact ferried P R W ρ h hP hs u ht e r i ⟨0,he⟩

lemma matter_out (e r):
    braise P R W (packV V L) ρ h (L.map μ).sum e r - packV (fun i=> braise P R W (V i) ρ h (μ i)) L e r=∑ i∈Finset.range ((L.map μ).sum+3*e+1), jetty (coastRight _ _ _) (morsel P R ρ W h V L i e r):= by
    let o:edgeL G:=(0,Exterior.coord 0,a); let u(n:Side):=(Classical.choice (chooseable n (n*P.patch.L) (primary P.patch K n))); let x:= chief P o o.2
    have H (T:Pot G)(l:ℕ)(ht':Ritual T l) i j:WavePath x (braise P R W T ρ h l i j) (fun n=> rancho (tossed P ρ h R n (u n) (Mesa.stone W _) (Kemp.banner l T _)) i j):= testified o P R W ρ h hP hs ht ht' u i j
    apply ((H (packV V L) (L.map μ).sum (orchestra V μ L hv a) e r).dust (flaring L e r (fun i hi=> H _ _ (hv i hi)))).agree
    have he (n:Side):=output_terms P R ρ W h n (u n) a V μ L hv hP hs ht e r
    let f (n: Side) (T:Pot G)(μ:ℕ):= tossed P ρ h R n (u n) (Mesa.stone W _) (Kemp.banner μ T _)
    change WavePath x _ (fun n: Side=> rancho (f n (packV V L) (L.map μ).sum) e r- packV (fun i=>rancho (f n (V i) (μ i))) L e r)
    have hx n : rancho (f n (packV V L) (L.map μ).sum) e r- packV (fun i=>rancho (f n (V i) (μ i))) L e r= ∑ i∈Finset.range ((L.map μ).sum +3* e+1), jetty (coastRight _ _ _) (Lava.posting (tectonic P R ρ W h n (u n) V μ L) i e r):= by rw [mountV]; exact (show rancho _ e r-rancho _ e r=rancho (f n (packV V L) (L.map μ).sum-(L.map fun i=> f n (V i) (μ i)).prod) e r from congr_fun (congr_fun (marred (f n (packV V L) (L.map μ).sum) _).symm e) r)|>.trans (he n)
    simp_rw [hx]
    apply wave_many _; intro i hi; obtain ⟨z,hz,H⟩:=pathE P R ρ W h u a o V μ L hv hP hs ht i e r; exact ⟨z,hz,kalm_cut H⟩
end YM.FormalBulk08.Vale
