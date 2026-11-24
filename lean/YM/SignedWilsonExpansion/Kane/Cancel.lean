import YM.SignedWilsonExpansion.Kane.Composure
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.Integration.Election
open RG RG.Supply Extraction PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec Climb Trace.Terrace Trace.Pilot
open Function Filter Lattice Wilson Source
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale.Level Future
open SignedWilsonExpansion.Belfry SignedWilsonExpansion.Belle SignedWilsonExpansion.Dancer SignedWilsonExpansion.Belfry.Crisis SignedWilsonExpansion.Belfry.Classroom SignedWilsonExpansion.Belfry.ScaleFits
open SignedWilsonExpansion.Kane.Tilted Scale MS MS.Native MS.High MS.Land MS.Fleet Asymptotics
open PhysMS Frame Order Spin Next.UVStress OPE OPE.Orbits
open PowerSeries Register
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge}{R:Run G}{h:G.Simple}
-- shoe adapter & post. do not identify clocks by convergence theorem only.
namespace Frames
variable {n d b j:ℕ} {ι:Type} {l: Filter ι} {f:Extraction.Order} {S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
variable (lead : PhysMS.Leading F J){V:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{Q:MS.Land.Prescription (Press.portDeck G)} (Z:WilsonPrescription G){dial:Bool}(H: Main.Match Z h V Q dial)
local notation "W"=> WilsonPositionPrescribedFrame.positioned F J Z.store
local notation "Θ"=> WilsonPositionHomogeneousFrame.reading F J Z
local notation "K₀"=> WilsonPositionHomogeneousFrame.homogeneous F J Z -- parser test
open SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Belfry SignedWilsonExpansion.Dancer FVA2.Scale Scale.GroupS
variable (s:G.Simple)(ν:ℝ) (r g:ι→ℝ)(u:Tendsto r l trail)(price:FO l g)
open WilsonPositionHomogeneousComparison MeasureTheory
variable (T:Crest F J Z)(L:Leading F (WilsonPositionPrescribedFrame.positioned F J Z.store)){Y:(Bel R.family.book).Hierarchy}(p:∀d:ℕ,∀ᶠ i in trail, obedient F Y (J i) d){P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}(X:Scaling S)(ξ:Foundation F P)
local notation "T₀"=> ( Θ∘r )
local notation "Ω"=> ( Scale.Measure.outlook Z.scheme Z.criterion )
private def roto (i:Fin (n+1)): Equiv.Perm (Fin (n+1)):= (finSuccEquiv n).trans (finSuccEquiv' i).symm
private lemma roto_at (i:Fin (n+1)) : roto i 0=i:=by simp [roto]
private lemma roto_after (i:Fin (n+1))(j:Fin n): roto i j.succ=i.succAbove j:=by simp[roto]
def lopU (i:Fin (n+1))(y: Points (n+1)) : Points n:= points fun j=>y (i.succAbove j)
private lemma use_unit (s:Viewers F) {x:Points (n+1)}(hx:x∈conf (n+1))(i:Fin (n+1))(v:Fin n→S.Tag):
   S.useAt (spectator F s) x (i.insertNth ⟨d,S.unit d⟩ v)= S.useAt (spectator F s) (lopU i x) v:=by
   let q : Fin n→ R.family.book.Token:=fun i=>⟨(v i).1, S.representative _ (v i).2⟩;let w:= Fin.cons (α:=fun _=>R.family.book.Token) (R.family.book.one d) q; let h:= spectate F s; let r:= roto i
   have he(j):S.classTokens (q j)=v j:=by change (⟨(v j).1,S.project _ (S.representative _ (v j).2)⟩:S.Tag)=_; rw [S.rep]
   have ht: i.insertNth (α:=fun _=>S.Tag) ⟨d,S.unit d⟩ v ∘ r=S.classTokens ∘ w:=by
       funext j; refine Fin.cases ?_ (fun p=>?_) j
       · simp only[Function.comp_apply,r,roto_at,w,Fin.cons_zero,Fin.insertNth_apply_same];rfl
       simp only [Function.comp_apply, w, Fin.cons_succ, he, r, roto_after, Fin.insertNth_apply_succAbove]
   rw [← S.class_perm _ h.laws.toSymmetric r hx, ht]; have hp:=Points.rearrange_in r hx
   rw[S.at_project _ h.laws.toSymmetric (spectate_respects F s) hp w,h.laws.unital hp d]
   rw[show (Points.rearrange r x).tail=lopU i x from ?_]; rfl
   ext1 z; change x (r z.succ)=_; rw [show r z.succ=i.succAbove z from roto_after ..];rfl
lemma tearPv (i:Fin (n+1))(x:Points (n+1))(p:x∈conf (n+1)): lopU i x∈conf n:=fun a b he=> Fin.succAbove_right_injective (p (show x (i.succAbove a)=x (i.succAbove b) from he))
abbrev ease (i:Fin (n+1))(x:Scale.Stage (n+1)): Scale.Stage n:= ⟨ lopU i x.val,tearPv i _ x.property ⟩
-- normalized moment. apply through arbitrary Viewers including none. unit at every cap.
lemma deleted (A:ℝ→tower S)(d:ℕ){r:ℝ}(t:0<r)(u:Sec G d)(ht:walk A r d u=S.unit d)(i:Fin (n+1))(v:Tags G d n)(x:Scale.Stage (n+1))(V:Viewers F): PlotW F A V r d (n+1) x.val ( i.insertNth u v )= PlotW F A V r d n ( lopU i x.val ) v:=by
      let y(k:Fin n): S.Tag:=⟨ d,walk A r d (v k) ⟩; change S.useAt (spectator F V) (r•x.val) (fun j=>⟨d,walk A r d ( i.insertNth (α:=fun _=> Sec G d) u v j )⟩) = S.useAt _ (r • lopU i x.val) y; rw [ ← show lopU i (r•x.val)=r•lopU i x.val from rfl, ← use_unit F V ( d:=d ) ( Work.A05.smul_conf t x.property ) i y ]; apply congr_arg; funext j; induction j using Fin.succAboveCases i <;> simp [y,ht] -- inspect defeq
-- cancellations: also SELF-test independent label polynomial on both frames, exact at this horizon.
lemma billZero (v:ℝ→ℝ)(p:∀ᶠ i in trail,0<v i)(a b:ℕ→ℂ)(h:∀ k,( fun i=> ( ∑ j∈ Finset.range (k+1),(v i:ℂ)^j*(a j-b j) ) )=o[trail] (v^k)): a=b:=by
    funext k; induction k using Nat.strong_induction_on with
    | h k ih=>
       by_contra hn; have h0: 0<‖a k-b k‖:= norm_pos_iff.mpr (sub_ne_zero_of_ne hn)
       obtain ⟨i,z,H⟩:= (((h k).bound (half_pos h0)).and p).exists
       rw [ Finset.sum_range_succ ] at z; have H'(j)(h:j∈Finset.range k):a j-b j=0:=sub_eq_zero.mpr (ih j (Finset.mem_range.mp h)); rw [ Finset.sum_eq_zero (f:=fun j=>(v i:ℂ)^j*(a j-b j)) (fun j h=> by rw [H' j h,mul_zero]),zero_add,norm_mul, norm_pow, Complex.norm_real, Pi.pow_apply,norm_pow,Real.norm_eq_abs,abs_of_pos H, mul_comm ] at z; nlinarith only [ z, pow_pos H k,h0 ]
include lead u p L h in
lemma revoked (i:Fin (n+1))(d:ℕ): ∀ᶠ j in l,∀ x:Scale.Stage (n+1),∀ u:Viewers F,∀ v: Tags G d n, PlotW F W u ( r j ) d (n+1) x.val ( i.insertNth (leaf G d) v )=PlotW F W u ( r j ) d n ( lopU i x.val ) v ∧ PlotW F K₀ u ( r j ) d (n+1) x.val ( i.insertNth (leaf G d) v )=PlotW F K₀ u ( r j ) d n ( lopU i x.val ) v:=by
      filter_upwards [ SpinW L u d,Frames.spins (h:=h) F J lead Z r u p L d,u.eventually self_mem_nhdsWithin ] with j hi ht hp x a v; exact ⟨ deleted _ _ _ hp _ hi.1 ..,deleted _ _ _ hp _ ht.1 .. ⟩ -- params
-- cancel every fixed order by induction. applicable on both.
local notation "λP"=> FVA2.Scale.Measure.start Z.scheme Z.criterion
include T lead p L H ξ X
lemma strippedCoeff (d b:ℕ)(t:Tags G d n)(j:Fin (n+1))(x:Scale.Stage (n+1)) : coefficient Z V ν d x (j.insertNth (Normalize.leaf G d) t) b=coefficient Z V ν d ( ease j x ) t b:=by
     let P': Tags G d (n+1):= j.insertNth (leaf G d) t; let v':= ease j x; have ε:= formally F J lead Z H T L p X ξ ν d P' {x.val} ⟨ isCompact_singleton,Set.singleton_subset_iff.mpr x.property ⟩; have δ:= formally F J lead Z H T L p X ξ ν d t {v'.val} ⟨ isCompact_singleton,Set.singleton_subset_iff.mpr v'.property ⟩; have hp:= T.clock.positive; refine congr_fun (billZero Θ hp (coefficient Z V ν d x P') (coefficient Z V ν d v' t) (?_)) b; intro k; apply IsLittleO.of_bound; intro c hc; filter_upwards [ ε k (c/2) (half_pos hc), δ k (c/2) (half_pos hc), revoked (l:=trail) (h:=h) F J lead Z id tendsto_id L p j d ] with i hv hu h'; specialize hv x (Set.mem_singleton _); specialize hu v' (Set.mem_singleton _); have e: observed Z F J d P' i x.val= observed Z F J d t i v'.val:= ( h' x none t ).2; rw [e] at hv; let a:= observed Z F J d t i v'.val; change ‖∑ _j∈Finset.range ( k+1 ),_‖ ≤_; simp_rw [ _root_.mul_sub,Finset.sum_sub_distrib ]; change ‖ polynomial Z V ν d x P' k ( Θ i )- polynomial Z V ν d v' t k ( Θ i  )‖≤_; rw [ Pi.pow_apply, norm_pow, Real.norm_eq_abs]; let w:= polynomial Z V ν d x P' k ( Θ i ); have e:= norm_sub_le_norm_sub_add_norm_sub w a (polynomial Z V ν d v' t k (Θ i )); rw [ norm_sub_rev w a ] at e -- should choose second not e lhs? inspect
     unfold w a at e; linarith
end Frames
end YM.Integration.Election
