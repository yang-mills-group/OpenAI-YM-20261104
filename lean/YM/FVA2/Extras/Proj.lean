import YM.FVA2.Extras.Curtain
/-! # The `service` formula and actually proving reexpression

Auxiliary to `YM/FVA2/Extras/Result.lean`. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
open Job.Belt Rake.Geo O.Hue O.Fuse O.Cool
variable {I:Type}{G:Gauge}{b d:ℤ}{r k n:ℕ}{B:Deck G}{K:Booked B}{M:MS_Data G K}
variable {W:Type}[LinearOrder W]{a:ℝ}{x: Position W Unit}{X Y:T (localX G)}{Q:W→T (localX G)}{i j:W}{s:Finset W}{h:ℕ}{p:T (Package B h)}{v:List W}
variable (x) (Q)
-- any nondependent assignments for extr.O. definitive convention as in 
-- supplied data, so not claiming comparison for other MS continuation choices.
open Classical in
def score (a:ℝ)(M:MS_Data G K)(x:Position W Unit)(Q:W→ T ( localX G )): Rake.Dance G Unit W:= if h: ∃ X:Rake.Dance G Unit W, Teams ( Tide.frameF Unit a ) M Q x X then h.choose else 0
variable {x Q}
abbrev service (a:ℝ)(M:MS_Data G K)(Q:W→T (localX G))(x:Position W Unit)(s:Finset W): T ℂ:= reported x (score a M x Q) () s
abbrev swapField (a:ℝ)(M:MS_Data G K)(i:W)(p:Plaid B h)(Q:W→ T (localX G)):= update Q i (soloV h (logMass a) M p)
variable (hW:Survey (Tide.frameF Unit a) M Q x)(hs:Mesh (Tide.frameF Unit a) x)
include hW hs
lemma scoreK : Teams (Tide.frameF Unit a) M Q x ( score a M x Q ):= by
    obtain ⟨Y,hK,_⟩ := epoch_s hW hs; have hV : ∃ X:Rake.Dance G Unit W, Teams ( Tide.frameF Unit a ) M Q x X:= ⟨Y,hK⟩; rw [score,dif_pos hV]; exact hV.choose_spec
-- on standard inputs agrees with supplied MS_Data endpoint
lemma tourC (U:W→ Rake.Label B)(hx:Q=rowM (Tide.frameF Unit a) M ∘ U)(s:Finset W)(i:ℕ): service a M Q x s i= Dial.tour M U a (fun i=>x i ()) s i:= by
    refine tendsto_nhds_unique ( total_peak ( plates hW ( scoreK hW hs ) (fun s i=> calls hW hs ( scoreK hW hs ) i s) s ) () i ) ?_; have h0:DOrd K (Tide.frameF Unit a) M U x ( score a M x Q ):= by subst Q; exact scoreK hW hs
    suffices hHt: Injective ( Dial.pointI x () ) from Fuse.ready h0 () hHt s i; intro j k h; by_contra H; obtain ⟨C,hC,hK⟩:= ( hs j k H).floor; specialize hK (); change C * exp (0:ℝ) ≤ ‖ (x j () ) - x k ()‖ at hK; change x j ()= x k () at h; simp [h,hC.not_ge] at hK
omit hs in
lemma swapped (V:Plaid B h)(i:W): Survey (Tide.frameF Unit a) M (swapField a M i V Q) x := by
    intro j; by_cases hj:j=i
    · subst j; rw [swapField,update_self]; exact Estate ( cometClean ( M.markOK h V )) ( Response.visit V ) _
    rw [ swapField, update_of_ne hj ]; exact hW j
local notation "Z"=> ( score a M x Q )
variable (H:v.Nodup)(Hv:i∉v)
include H Hv
private lemma valid_insert (r:Plaid B h): let U:=swapField a M i r Q; Lucent (Tide.frameF Unit a) M 0 ( plenum x (score a M x U) (insert i v.toFinset) ) ( nest ( v.map ( note x Q ) ) ( x i ) ( soloV h (logMass a) M r ) ):= by
    intro U; obtain he:=swapped hW r i; have h': v.map (note x U) = v.map (note x Q):= List.map_congr_left (fun j hj=> by unfold note U swapField; rw [update_of_ne ( show j≠i from fun e=> Hv (e ▸ hj))]); obtain hZ:=scoreK he hs; obtain hp:=scene ( i:=i ) hZ he hs rfl H Hv; change Lucent _ _ _ ( plenum x (score a M x U) _ ) (nest ( v.map (note x U) ) ( x i ) ( U i )) at hp; rw [h',show U i=_ from ( show U i= soloV _ (logMass a) M r from update_self .. ) ] at hp; exact hp
lemma apply_one (he:Q i=X)(hm:X=many a M p+nav M (logMass a) Y)(hp:ghostly a M Y ((h:ℤ)-1))(hV:∀ i∈v,nav M (logMass a) (Q i)=0): let s:= insert i v.toFinset; service a M Q x s n=∑ k:Plaid B h,∑ j∈Finset.range (n+1),(p j k:ℂ)* service a M (swapField a M i k Q) x s (n-j):= by
    subst X; intro s; let Y i:= plenum x (score a M x i) s; exact upland (L:=v.map ( note x Q )) ( x:=x i ) (U:=fun p=> Y ( swapField a M i p Q )) hm ( scene ( scoreK hW hs ) hW hs rfl H Hv ) hp ( apart_scene hW hs H Hv ) ( valid_insert hW hs H Hv ) ( by intro j hj; obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hj; exact ⟨ (hW r).1,hV r hr⟩ )
omit hW hs H Hv
/-- Any one approved composite row under this MS convention can be projected after specialization. 
    Does not require separate Taylor poles for evanescents. One can replace EVERY redundant input
    at its own horizon this way, since all exteriors may also use any such closed rows.
    Common assignment on inserted slot. No asserting yet which purely dimensional evanescents
    vanish at which orders; keeps their induced exact contributions.
 -/
theorem rewrite_extra (hX:Forth a M X h): ∃ p:T (Package B h), ∀ (W:Type)(_ : LinearOrder W)(x: Position W Unit)(Q:W→T (localX G))(i:W), Q i=X→ Survey (Tide.frameF Unit a) M Q x→Mesh (Tide.frameF Unit a) x→∀ s:Finset W,i∈s→ (∀ j∈s,Certified ( Q j ) M (logMass a) 0)→∀ n, service a M Q x s n=∑ k:Plaid B h,∑ j∈Finset.range (n+1), (p j k:ℂ) * service a M (swapField a M i k Q) x s (n-j) := by
    obtain ⟨p,Y,hY,hp⟩:= cleanMultiple hX; refine ⟨ p,fun W _ x Q i hi hW hs s ht hS n=> ?_⟩; let v:= (s.erase i).toList; obtain he:= apply_one ( n:=n ) hW hs ( Finset.nodup_toList (s.erase i) ) ( by simp ) hi hp hY (fun i hi=> ( hS i ( Finset.mem_of_mem_erase ( Finset.mem_toList.mp hi ) ) ).2 ); simpa only [ Finset.toList_toFinset,Finset.insert_erase ht ] using he
end YM.FVA2.Extras
