import YM.WilsonCoeffUV.Winding.Moment
/-!
# Mer: auth and all alias fibers. Geometric authorization on any torus.
Not an endorsement of any mask or of preimage-summed mixed kernels after k<->coarse shifts.
Mark positions retained within chosen hull. -/
set_option autoImplicit false
set_option maxHeartbeats 560000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Wheel Wheel.Mark Cosmos Mer Function Filter Lattice RG Embroider Soil Bank Laurent Bloch Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent AnalyticNext.QuarticMatch.Sheets PowerSeries Bank.Mosaic Bank.Carp
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β T:Type}{V:Type}{G:Gauge}{D k:ι→ℕ}{Ñ:ChartRatio G}{m N k' i j r e a l:ℕ}{s A B C W t q :ℝ}
variable {J Z S:Finset ι}{p:ι→Cover}
variable [NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
open Mer.Rolls
omit [CompleteSpace V] in
lemma night_sky {P: Era G V}(h:Auth i P)(e:ℕ):∃ s C,0<s∧ Rain P.2 e s C:=by
    induction e with
    | zero=> exact ⟨1,0,one_pos,le_rfl,by intro i v; omega⟩
    | succ e ih=>
       obtain ⟨s,b,u,H⟩:=ih; let J (r:ℕ):= (h.wing e r).land; have hh:∀ t:Fin (i+e+1), ∃ z c:ℝ,0<z∧ Cork Bank.terrain 0 z c (P.2 e t.val):=fun t=>J _
       choose z c f g using hh; let v:= Finset.univ.inf' Finset.univ_nonempty z; have he :0<v:=(Finset.lt_inf'_iff _).mpr fun j _=> f j
       let B:=∑ i,c i; let w:=min v s; have hp:0<w:=lt_min he u; have hc j:0≤ c j:= (g j).1; have hb:0≤ B:= Finset.sum_nonneg (fun i _=>hc i); refine ⟨w,B+b,hp,add_nonneg hb H.1,?_⟩
       intro j p' r; by_cases v:j=e; swap; · exact ((H.2 _ (by omega) r).mono (min_le_right ..)).cost (le_add_of_nonneg_left hb)
       subst j
       by_cases eq:r< i+e+1
       · let j:Fin (i+e+1):=⟨_,eq⟩; have hv:= Finset.single_le_sum (fun i _=> hc i) (Finset.mem_univ j); exact ((g j).mono ((min_le_left ..).trans (Finset.inf'_le z (Finset.mem_univ j)))).cost (hv.trans (le_add_of_nonneg_right H.1))
       rw [h.coverN e r (by omega)]; exact Cork.zero.cost (add_nonneg hb H.1)

def remade (F: Era G V): Era G V:= (fun n i j=> Bank.Carp.plume (F.2 i j) n, F.2)
omit [NormedSpace ℝ V][CompleteSpace V] in
lemma remake_zero: remade (0:Era G V)=0:= Prod.ext (funext fun _=>funext fun _=>funext fun _=>Bank.Carp.plume_zero _) rfl
lemma remake_charge {P: Era G V}(p:Auth k' P): Auth k' (remade P):=by
   have he i:∃ Q:Era G V, Auth k' Q ∧ ∀ n,∀ j< i, Q.1 n j=(remade P).1 n j:=by
       obtain ⟨s,A,v,c⟩:= night_sky p i; obtain ⟨t,C,b,w,x,H⟩:= autoK G s i k' v; obtain ⟨q,Q⟩:= H i le_rfl V P.2 A (nimb P p i) c; let X:= baton (automa P.2 k' i) i; refine ⟨X, sufficesR q b,fun n j v=> ?_⟩; funext k; change X.1 n j k= Bank.Carp.plume _ _; have h'k:X.1 n j k=Bank.Carp.plume (X.2 j k) n:= Mer.Rolls.mooring q b n j k; rw [h'k,Q j v]
   refine ⟨fun i j=> ?_,fun n i j v=>?_,fun n i j=>?_,?_⟩
   · obtain ⟨s,A,h,v⟩:= (p.wing i j).land; exact caisson v h
   · obtain ⟨X,q,g⟩:= he (i+1); rw [← g n i i.lt_succ_self]; exact q.span n i j v
   · obtain ⟨X,q,g⟩:= he (i+1); rw [←g n i i.lt_succ_self]; exact q.pale n i j
   intro n t Z I a U V u; let Q:=remade P
   ext1 j; obtain ⟨X,q,g⟩:=he (j+1); have h: Equal (j+1) (Blue.flash (ply t (X.1 n))) (Blue.flash (ply t (Q.1 n))):=by
       intro i p; simp only [Blue.flash,coeff_mk]; apply congr_arg totalR; funext k x; exact congr_arg t (congr_fun (congr_fun (g n i p) k) x)
   have hv (S:Lawn Z→Lawn (Woods G n)):= filtered (ξ:=train (spool S)) (by simp) h j j.lt_succ_self
   exact (hv U).symm.trans ((congr_arg (PowerSeries.coeff _) (q.token n t u)).trans (hv V))

-- inputs in PackOne remade. cover operation never observes reparity of aliases.
def repaint (P: family G D): family G D:=fun x=> remade (P x)
lemma repose {P: family G D} (p:Eu k P): Eu k (repaint P):= fun i=> remake_charge (p i)
lemma toned [DecidableEq ι] {P: family G D} {I: Arch G}(C:ScrollV e I): Humour I.P I.K I.R C.γ C.M C.Z (repaint P)= Humour I.P I.K I.R C.γ C.M C.Z P:=rfl

-- unmarked publication

def emera (P:Bank.Canvas G): Crude G:= fun n j r=> match r with
    | 0=> 0
    | _+1=> lagoon (P j _) n
lemma emera_forms (P:Bank.Canvas G)(g:shellK k' P) (h:∀ i,Pure (P i))(x: ∀ i j,stroll (P i j))(n:Side): shellK k' (emera P n)∧∀ i, Pure (emera P n i):=by
   constructor
   · intro i j v; cases j with
     | zero=> rfl
     | succ j=> change lagoon (P i (j+1)) n = _; rw [g i (j+1) v, lagoon_none]
   intro i j; cases j with
   | zero=> exact Blue.Smooth.zero
   | succ j=> exact lagoon_smooth _ (h i _) (x i _) n
lemma emera_far (A:Levels G)(p:G.Simple)(h:LocalRatio Ñ)(b:N≤m)(n):
     let P:= actionW A Ñ m N
     shellK 2 (emera P n)∧∀ i,Pure (emera P n i):=by
    let V:=old A Ñ p h m N b
    apply emera_forms
    · exact (catchment A Ñ p h b).rank
    · exact fun i j=> (V.patch i j).sym (Eventually.of_forall fun n=> (V.basis n).shape i j)
    exact fun i j=>(V.patch i j).road
end YM.WilsonCoeffUV.Winding
