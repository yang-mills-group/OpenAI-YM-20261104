import YM.MS.Awning.Span
/-!
# External polynomial degrees. Finite value tests.
Linear constraints can be tested at any stage of Laurent/ODE construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Awning
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Signal Book Convolve
open scoped Topology ContDiff Interval
variable {G:Gauge}{E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{X:Type}{p h:ℤ}{m n:ℕ}{F H: Mob G}
-- h will be weight-minus-rank
def PriceR (h:ℤ)(w: Legs (Mode (Cfield G m) X)) : ℤ:= h-mass w+(w.length:ℤ)
lemma price_M (hp:m≤n)(W:Touch G m E) : PriceR h (move hp W)=PriceR h W:= by unfold PriceR; rw [← mass_sail (move hp W) (0:E), ← moves,mass_lift,mass_sail]; simp [Rock.move]
lemma price_1 (t:Cfield G m): 1≤ wfield t:=by unfold wfield Landau.dim; cases t.1.2 <;> simp
lemma price_S (i : Mode (Cfield G m) X)(w): PriceR h (i::w)≤ PriceR h w:= by simp only [PriceR,Price_cons,List.length_cons,Nat.cast_add,Nat.cast_one]; have ht:= price_1 i.1; omega
abbrev Caper (h:ℤ)(F:Mob G): Prop:=∀ (m:ℕ)(E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E], ∀ W:Touch G m E,∀ x v:E,(fun t:ℝ=> F m (sail W (x+t • v))) ∈ Bowl (PriceR h W)
def CapAir (h:ℤ)(G:Gauge): LeanC G where
    carrier:= Caper h
    zero_mem':= fun _ _ _ _ _ _ _ _=> ( Bowl _ ).zero_mem
    add_mem' {X Y} h he m E _ _ _ W x v:= (Bowl _).add_mem (h m E W x v) (he m E W x v)
    smul_mem' c _ H m E _ _ _ W x v:= ( Bowl _ ).smul_mem _ (H m E W x v)
lemma Walked (hF:F∈CapAir h G)(u:ℂ)(s:ℝ): plow u s F∈CapAir h G:= by
    intro m E _ _ _ W x v; change (fun t:ℝ=> fieldVal (plow u s F m) W (x+t • v))∈_; simp_rw [s_p_vector, smul_add, smul_comm (exp s) (_:ℝ) v]; exact ( Bowl ( PriceR _ W ) ).smul_mem (amount _ _) (hF m E W (exp s • x) ( exp s • v ))
-- instance changes
lemma Needed (h:ℤ): Need ( CapAir h G ) where
   touch:= by intro I L _ f F H he; intro m E _ _ _ W x v; replace he : ∀ᶠ i in L,Caper h (f i):= he; apply (bowl_iff _).mpr; intro s μ hμ; exact tendsto_nhds_unique ( tendsto_finsetSum _ fun t _=> Tendsto.const_mul ( μ t ) ( H m (sail W (x+t • v)) ) ) (tendsto_const_nhds.congr' (he.mono fun i hi=> ((bowl_iff _).mp (hi m E W x v) s μ hμ).symm))
   walk _ s h:= Walked h 0 s
   runner:= by
      intro u t ht hU; intro m E _ _ _ W x v; apply (bowl_iff _).mpr; intro s μ hμ; replace hU:∀ i,Caper h (u i):=hU; unfold mend; simp_rw [← integral_const_mul]; rw [← integral_finsetSum _ (fun i _=> ((ht m (sail W (x+i • v))).const_mul (μ i)) ) ]; simp_rw [show ∀ p,∑ i∈ s,μ i * u p m (sail W (x+i • v))=0 from fun p=> (bowl_iff _).mp ( hU p m E W x v ) s μ hμ]; simp
-- Contracting with arbitrary constant line preceded. Sight Ward.
lemma twin (hF:F∈CapAir h G)(i j: Shore G m)(W:Touch G m E)(x v:E) : (fun t:ℝ=> F m (i::j::sail W (x+t • v)))∈Bowl (PriceR h W):= by
    let L:= ContinuousLinearMap.fst ℝ E ℝ; let X:Touch G m (E×ℝ):= Wire.lift W L; let A(k: Shore G m): Mode (Cfield G m) ((E×ℝ)→L[ℝ] SectorP m):= (k.1, (ContinuousLinearMap.snd ℝ E ℝ).smulRight k.2 ); let R:= A i::A j::X
    have he (t:ℝ): sail R ((x,(1:ℝ))+t • (v, (0:ℝ)))= i::j::sail W (x+t • v):= by simp [R,X,L,A]
    obtain hp:= hF m (E×ℝ) R (x,1) (v,0); simp_rw [he] at hp; rw [show PriceR h W= PriceR h X from ?_]; exact bowl_more ((price_S ..).trans (price_S ..)) hp -- Max dimension lemma args
    unfold X PriceR mass; simp [Wire.lift]; rfl
lemma stock (hF:F∈CapAir h G)(W:Touch G m E)(r:Rip G)(p:SectorP m)(x v:E): (fun t:ℝ=> trc (r m) p (F m) (sail W (x+t • v)))∈ Bowl ( PriceR h W ):= by
    simp_rw [at_trc]; convert! (Bowl (PriceR h W)).sum_mem (t:=univ) (f:=fun i:Cfield G m=>∑ j:Cfield G m, r m i j p • (fun t:ℝ=> F m ((i,p):: (j,-p)::sail W (x+t • v)))) (fun i _=> (Bowl (PriceR h W)).sum_mem fun j _=> ( Bowl (PriceR h W) ).smul_mem (r m i j p) (twin hF _ _ W x v)) using 1; ext; simp
lemma stockV {r: Rip G} {b:Bool} (hp: Form0 b F)(hr:Knot b r)(hF: F∈ CapAir h G)(x v:E)(W:Touch G m E)(p:SectorP m)(k:ℂ): (fun t:ℝ=> Wtr k r F p (sail W (x+t • v)))∈ Bowl ( PriceR h W ):= by
    have he (n:ℕ)(hm:m≤n): (fun t:ℝ=> Wtr (n:ℂ) r F p (sail W ( x+t • v)))∈ Bowl (PriceR h W) := by
       simp_rw [tallyN hp.token hr.token hm,Rock.moves hm]; rw [ ← price_M hm W ]; exact stock hF _ r _ x v -- price ty hole
    simp_rw [combo k m, Pi.add_apply,Pi.smul_apply,Pi.sub_apply]; exact ( Bowl (PriceR h W) ).add_mem (he m le_rfl) (( Bowl (PriceR h W) ).smul_mem (k-m) (( Bowl (PriceR h W) ).sub_mem (he _ ( Nat.le_succ m )) (he m le_rfl)))
end YM.MS.Awning
