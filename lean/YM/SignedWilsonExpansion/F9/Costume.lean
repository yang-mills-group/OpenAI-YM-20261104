import YM.SignedWilsonExpansion.F9.Desk
/-!
# Costume and Grade ledger
Board α weights realized at exact doorway using SAME snaps. Use earned clocks via `sponsored`. Retest economy across ears using exact identity with Boots. 
-/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c b N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace MarqueQ
open SignedWilsonExpansion.Commission Method Method.Epic Asymptotics Stair MergeTrip Looms
open Normalize (Sec)
open XSpace.Cirrus
variable {W':Initialize G}{Q':∀ h,Rays G h W'.hol}{Ω:Council F}
variable {P':Hol G}{ι:Type}{A':SectionData (F.level d)}
lemma Respect.allRank (h:Auth k P) (e d:ℕ): ∃ C:ℝ, Respect k e d 1 P C:=by
    choose C hC using fun i j=> attends h i j d -- signature
    let S:= Finset.univ (α:= Fin (e+1) × Fin (k+e+1)); let f (x : Fin (e+1) × Fin (k+e+1)):= C x.1 x.2
    have he(i:Fin (e+1)×Fin (k+e+1)): 0≤ f i:= (hC i.1 i.2).C
    refine ⟨(∑ i∈ S,f i),h,fun i hi j hj=>?_⟩; by_cases v:k+e<j; · rw [h.coverN _ _ (by omega)]; exact Fruit.zero.more (Finset.sum_nonneg (fun i _=> he i))
    exact (hC i j).more (Finset.single_le_sum (s:=S) (f:=f) (fun i _=> he i) ( Finset.mem_univ ((⟨i,by omega⟩,⟨j,by omega⟩):Fin (e+1)× Fin (k+e+1))))
namespace PorchK
variable (x:PorchK W' F Q' Ω R h k u) (q:ι→ PorchK W' F Q' Ω R h k u)(Wn : Normalize.Store G)
variable {Y B:ι→ℝ} {L:Filter ι}(hQ:Annual q L Y)
section shape
variable (A':SectionData (F.level d)) (hA:A'.Sound P')(hp:Bid.pop A')(v:d≤h)
abbrev tap (α:(F.level d).Index)(β:(F.level h).Index) := x.canv.pushTax W' A' α β x.l x.r x.ρ
abbrev markW := x.πMark x.v
def booth (α:(F.level d).Index)(β:(F.level h).Index) :=Tape.starE (x.tap A' α β) (x.canv.boots W' Wn x.mesh β x.l x.r x.ρ)
abbrev sober (α:(F.level d).Index) (z:ℕ) := x.canv.shapeD W' A' Wn x.mesh α x.l x.r x.ρ z
variable (α:(F.level d).Index)(β:(F.level h).Index)
lemma wearing {m w:ℕ}(P:Sec G h)(u:w≤h)(p:P∈Folia G w h)(ht:w < m): Normalize.part h m P=0:=by
    let X : Sec G w:= ⟨P.val,p⟩; rw [show P= Normalize.up u X from rfl,Normalize.part_up]; exact Normalize.part_zero ht X -- w shadow
lemma goesPart (i:ℕ): x.booth Wn A' α β i∈ Folia G (wt Rι β) h:=by
    unfold booth Tape.starE; apply Submodule.sum_mem (Folia G (wt Rι β) h) -- wrong order
    exact fun j _=> Submodule.smul_mem (Folia G (wt _ β) h) _ ( x.canv.boot_rank W' Wn x.mesh β _ )
include hQ hA hp v
lemma tap_charge : charge e L Y (fun i=>(q i).markW^(wt (F.level h) β)) (fun i=> (q i).tap A' α β):=by
    rcases isEmpty_or_nonempty ι with p|p -- need v≥ not depending on q.Derive from nonempty, trivial bot
    · exact fun _ _=> Wage.enroll (IsBigO.of_bound' (Eventually.of_forall fun i=> isEmptyElim i)) -- check name
    let i:ι:= Classical.choice p
    let C:= writePrice W'.hol F Ω k h e u E; obtain ⟨c,hc⟩:= Respect.allRank (strength (x:=α) A' hp hA (v.trans ((q i).canv.reserve W'.hol).order)) e u
    have he(x:PorchK W' F Q' Ω R h k u) : FitsZ e (insertQ (x.canv.tax (l:=x.l) (ρ:=x.ρ) A' α β)) (C.buy x.Z*(c*x.markW ^ wt _ β)):= FitsZ.written (x.canv.feesSphere W'.hol x.cost (x.datum.trans x.landing) x.pos β hc)
    let B(i):=(q i).markW^wt (F.level h) β; have ht:= charge.term C (B:=fun i=> c*(q i).markW ^ wt _ β) _ hQ.2 (Eventually.of_forall fun i=> he (q i))
    exact fun j w=> Wage.clip ((charge.ears _ hQ _ ht) j w) (isBigO_const_mul_self ..)
-- ticket cutoff can take ALL reachable Probe.size prices at actual K. Boundary placement fees fixed per d, even with periods after removing.
variable (Pp:∀ i≤ e, Across L Y ℂ (fun j=>(q j).toEpic.tenor W' Wn i))
include Pp
lemma booth_paid (v':j≤e): Salary L Y (fun i=>(q i).markW^wt Rι β) ℂ (fun i=> (q i).booth Wn A' α β j):=by
    let Q:=fun i=>(q i).tap A' α β; simp only [PorchK.booth,Tape.starE, Tape.pep,LinearMap.coe_mk,AddHom.coe_mk]; apply Salary.many hQ.1; intro i p; have h:i.1+i.2=j:= by simpa using p
    let f:= tap_charge q hQ A' hA hp v α β; simpa only [mul_one] using Salary.tilt (f i.1 (by omega)) (sponsored q Wn hQ Pp β i.2 (by omega))
lemma sober_paid (i':j≤e): Salary L Y 1 ℂ (fun i=> (q i).sober Wn A' α j):=by
    unfold sober shapeD; simp only [Finset.sum_apply]; apply Salary.many hQ.1; intro t _; refine Salary.transfer (booth_paid q Wn hQ A' hA hp v α t Pp i') (Wage.enroll (IsBigO.of_norm_le (fun i=>?_)))
    rw [Real.norm_of_nonneg ?_]; swap; · exact pow_nonneg (sizeT_pos _ (q i).pos _).le _
    exact pow_le_one₀ (sizeT_pos _ (q i).pos _).le (q i).small
lemma upper_bills (j n:ℕ)(hn:n≤h)(hv:j≤e): Salary L Y (fun i=>(q i).markW^n) ℂ (fun i=> Normalize.part h n ((q i).sober Wn A' α j)):=by
    unfold sober shapeD; simp only [ Finset.sum_apply, map_sum]; apply Salary.many hQ.1; intro i hk; by_cases he: n ≤ wt Rι i; · refine Salary.transfer ((booth_paid q Wn hQ A' hA hp v α i Pp hv).pass (Normalize.part h n)) (Wage.enroll (IsBigO.of_bound' (Eventually.of_forall fun x=>?_))); change ‖(q x).markW ^ wt Rι i‖ ≤ ‖(q x).markW ^ n‖; let t:=(q x).markW; have hx:0<t:= sizeT_pos _ (q x).pos _; rw [ Real.norm_of_nonneg (pow_nonneg hx.le _), Real.norm_of_nonneg (pow_nonneg hx.le _)]; exact pow_le_pow_of_le_one hx.le (q x).small he
    change Salary L Y _ ℂ (fun x=> Normalize.part h n ((q x).booth Wn A' α i j)); simp_rw [wearing _ ((F.level h).bound i) (goesPart ..) (Nat.lt_of_not_ge he),Salary,map_zero]; exact fun i=> Wage.nil
end shape
end PorchK
end MarqueQ
end YM.WilsonCoeffUV.Mer.Xa
