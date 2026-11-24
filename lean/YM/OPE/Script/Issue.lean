import YM.OPE.Pulse.Crop
import YM.Push.GRID_APPROXIMATION.Many
/-!
# Integral recovery for scripts with nested interactions applied to a portion
of each cell

Test at cells WITHOUT special mark (ledger). The old marks in such cells
may still be full and interacting; only require that there is no **specially
loaded** mark included. Mark/cell map can be restricted later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Patrol
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory Set
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open GridApprox Cells Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}{I J : Type} [Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    {A:History G} -- G implicit missing
set_option quotPrecheck false
local notation "K" => Finset
-- def ledger possibly for any mask
variable {N p i j k : ℕ} {s: i≤N}
local notation "V" => Site (A.S.side j p)
local notation "R" => A.rep N p
local notation "f" => A.S.side N p
local notation "c" => A.S.side i p
local notation "T" => tilesAt A.S p
local notation "β" => A.β N p N
structure Safe (A: History G) (N p : ℕ) (h:j ≤ i) (E : Site (A.S.side j p)) (F: Config G (A.S.side i p)→ℂ) : Prop where
   owns (a:ℕ)(ha:i ≤ a)(he:a ≤ N): Interior ((tilesAt A.S p (h.trans ha)).chamber E) (backTo A N p ha F)
namespace Safe
variable {u: Site (A.S.side j p)}{F:Config G (A.S.side i p)→ℂ}{h:j ≤ i}
lemma calls (hp: Safe A N p h u F)(hx:i ≤ N): Envelope F:= cylinder_env (show Interior _ F from by simpa using (hp.owns i le_rfl hx))
lemma seen {t:ℕ}(he:GridApprox.room A.levels j i t)(hp : Interior (GridApprox.window (anchor A.S p h u) t) F) : Safe A N p h u F:= ⟨fun _ hv _=>(backTo_local A N p h hv u t hp).enlarges (room_fits p A.levels t h hv he u)⟩
lemma resumes (h:i ≤ k) {v}(he:k ≤ v) (F : Config G (A.S.side i p) →ℂ):
    backTo A N p he (backTo A N p h F)=backTo A N p (h.trans he) F:=by
    induction v, he using Nat.le_induction with
    | base=>simp
    | succ m he ih=> rw [backTo_next A N p he, ih, backTo_next A N p (h.trans he)]
lemma passed (hp:Safe A N p h u F) (ht:i ≤ k) : Safe A N p (h.trans ht) u (backTo A N p ht F):=by
    refine ⟨fun _ hv he=>?_⟩; rw [resumes ht]; exact hp.owns _ (ht.trans hv) he
lemma passage (hi:i ≤ k) (hk:k ≤ N) {s:Finset (Site (A.S.side j p))}{F:Site (A.S.side j p)→ Config G (A.S.side i p)→ℂ}(hf:∀ i∈s,Safe A N p h i (F i)) : backTo A N p hi (fun U=>∏ i∈s,F i U)= fun U=> ∏ i∈s,backTo A N p hi (F i) U:=by
   induction k,hi using Nat.le_induction with
   | base=>simp
   | succ m hi IH=> simp_rw [backTo_next A N p hi,IH (by omega)]; exact back_cells _ (A.levels.blocks ..).branches _ (T (h.trans hi)) _ _ (fun i he=>(hf i he).owns m hi (by omega))
end Safe
/-- Exact recovery rule at shared copies. -/
def fineJob (F:I→ Config G n→ℂ)(a: K I) (U:Config G n):= ∏ i∈a,F i U
structure Script (A:History G)(N p:ℕ){i j:ℕ}(hq:j ≤ i)(hz:i ≤ N)(τ:I→Site (A.S.side j p))(d : K I)(Q:Config G (A.S.side i p)→ Poly (Bud I))(F:I→ Config G (A.S.side N p)→ℂ):Prop where
    budget : Integrable Q (prior G _)
    cost i: Envelope (F i)
    exists_budget (a: K I) (b: K (Site (A.S.side j p))) (h:Disjoint b ((a∩d).image τ)) (U: Site (A.S.side j p)→ Config G (A.S.side i p)→ℂ) (he:∀ i∈b,Safe A N p hq i (U i)) :
       (∫ W,(Q W).part (Fibers.mark a)*(∏ i∈b,U i W)∂ prior G _)= ∫ W,(bare (A.β N p N) W:ℂ)*fineJob F a W*(∏ i∈b,backTo A N p hz (U i) W)∂prior G _
namespace Script
variable {z: I→Site (A.S.side j p)}{F:I→ Config G (A.S.side N p)→ℂ} {hk:j ≤ i} {hz:i ≤ N} {Q:Config G (A.S.side i p)→ Poly (Bud I)} {d : K I}
lemma born(he:j ≤ N)(F:I→ Config G (A.S.side N p)→ℂ) {z:I→Site (A.S.side j p)} (h:A.Selected) (hr:∀ i,Envelope (F i)) : Script A N p he le_rfl z d (birth (Bud I) (A.rep N p N) F) F:=by
   have hx (s : (Bud I).Mode) (x):(birth (Bud I) (R N) F x).part s=(bare β x:ℂ)*(∏ i∈s.val,F i x):=by simp_rw [birth, Poly.part_smul,Mach,pass_fire,(h.starts ..).2]
   have hb : Envelope (fun U:Config G (A.S.side N p)=> (bare β U:ℂ)):= Envelope.compactC (Complex.continuous_ofReal.comp (bare_cont _))
   refine ⟨MeasureTheory.integrable_pi_iff.mpr (fun i=>?_),hr,fun a b hp U he=>?_⟩
   · change Integrable (fun x=>(birth (Bud I) (R N) F x).part i) _; simp_rw [hx]; exact (hb.mulC (Envelope.prodC i.val F (fun i _=>hr i))).integrableC _
   simp_rw [hx, backTo_self]; rfl
lemma step {he:j ≤ k}{hn:k ≤ i}(hp: Script A N p hk hz z d Q F): Script A N p he (hn.trans hz) z d (gust A N p i Q k hn) F:=by
   refine ⟨gust_live _ _ _ _ _ hp.budget _,hp.cost,fun a b h U hU=>?_⟩
   let s:= Fibers.mark a; let Q':= fun U=>(Q U).part s; let F':= fun W=>∏ i∈b,U i W; have hc := pushTo_dual A N p hn (Envelope.prodC b U (fun i hi=>(hU i hi).calls (hn.trans hz))) Q' (((Poly.get s).restrictScalars ℝ).integrable_comp hp.budget)
   have ht:= Safe.passage hn hz hU; have hz':=hp.exists_budget a b h (fun i=>backTo A N p hn (U i)) (fun i hi=> (hU i hi).passed hn)
   simp_rw [Safe.resumes hn hz] at hz'; rw [ht,hz'] at hc; simp_rw [← hc]; refine congr_arg (fun f':Config G (A.S.side k p)→ℂ => ∫ W,f' W*F' W∂ prior G _) (gust_choose A N p Q hp.budget hn s)
lemma gathered (Δ:Fibers I J)(hp: Script A N p hk hz z d Q F)(h:∀ i,z (Δ.twig (Δ.bunch i))=z i): Script A N p hk hz (z ∘ Δ.twig) (d.image Δ.bunch) (fun U=>Fibers.reap Δ (Q U)) (fun j=> fineJob F (Δ.contents j)):=by
   refine ⟨(Δ.reap.restrictScalars ℝ).integrable_comp hp.budget,fun j=> Envelope.prodC _ _ (fun i _=>hp.cost _), ?_⟩
   intro a b he U hf; let s:= Fibers.mark a; let B:= (Δ.plena s).val; have hh : Disjoint b ((B∩d).image z):=by
     apply Finset.disjoint_left.mpr; intro i hi hj; obtain ⟨j,hk',rfl⟩:= mem_image.mp hj; exact Finset.disjoint_left.mp he hi (mem_image.mpr ⟨Δ.bunch j,mem_inter.mpr ⟨(Δ.reaped ..).mp (Finset.mem_inter.mp hk').1, mem_image_of_mem _ (Finset.mem_inter.mp hk').2⟩, h _⟩)
   have hE:=hp.exists_budget B b hh U hf; simp_rw [show ∀ U,fineJob F B U=fineJob (fun j=>fineJob F (Δ.contents j)) a U from fun U=>Δ.prod_plena s (fun i=>F i U)] at hE; exact hE
end Script
end YM.MergeProof.Ribbons.ManyCopies.Patrol
