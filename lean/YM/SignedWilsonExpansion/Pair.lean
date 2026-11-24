import YM.SignedWilsonExpansion.OrderHigh
namespace YM.SignedWilsonExpansion.PhasePair
/-! # Cohort of independent mark-mask words using the actual fields

Mask = all for the connected pair. No mean-field term lost at this stage on
the independent model either. `Cabin` uses ``bill X q`` orientation. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open MS.Puff MS.Osc MS.Osc.Snap MS.Latch MS.Latch.Job MS.Rake.Geo MS.Rake MS.Rock MS.Rock.Path MS.Breeze MS.Vane
open FVA2 TreeView HighRank HighScale MarkRows MassShift MarkShift
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{f F H H':Law G}
local notation "Φ" => (PlanetD G)
local notation "μ" => covMeasure Axis

section calculus
variable {I:Type} (t:ℝ) (p:QP)
lemma mark_permit (he:F∈ Wallet G)(hp:H∈ Wallet G) : SatP μ (Φ t) F H p:= Wallet.hall he hp t p
lemma mark_sum1 (h:f∈Wallet G)(he:F∈ Wallet G)(hp:H∈ Wallet G):
    Cabin p (Φ t) μ (f+F) H= Cabin p (Φ t) μ f H+ Cabin p (Φ t) μ F H:= by
    have H:= sift (mark_permit t p ( (Wallet G).add_mem h he ) hp ) ( mark_permit t p he hp ); rw [ add_sub_cancel_right ] at H; exact (eq_sub_iff_add_eq.mp H).symm
lemma mark_sum2 (h:f∈Wallet G)(he:F∈ Wallet G)(hp:H∈ Wallet G):
    Cabin p (Φ t) μ H (f+F)= Cabin p (Φ t) μ H f+ Cabin p (Φ t) μ H F:= by
    have H:= sift' (mark_permit t p hp ( (Wallet G).add_mem h he ) ) ( mark_permit t p hp he ); rw [ add_sub_cancel_right ] at H; exact (eq_sub_iff_add_eq.mp H).symm
lemma mark_finL (S:Finset I) {V:I→Law G} (h:∀ i∈S, V i∈Wallet G) (he:F∈Wallet G) :
    Cabin p (Φ t) μ (∑ i∈S,V i) F=∑ i∈S,Cabin p (Φ t) μ (V i) F:= by
    induction S using Finset.induction with| empty=> simp only [Finset.sum_empty]; unfold Cabin; funext w; rw [scatter_congr _ _ _ ( fun _ _=> (0:ℂ) ) ?_]; exact map_zero (allocate ..); intro _ _ _; simp [meshZ]| insert i s hi ih=> have hx j hj:= h j ( Finset.mem_insert_of_mem ( b:=i ) hj ); rw [ Finset.sum_insert hi, Finset.sum_insert hi, mark_sum1 t p ( h _ (by simp) ) ( Submodule.sum_mem _ hx ) he, ih hx ]
lemma mark_finR (S:Finset I) {V:I→Law G} (h:∀ i∈S,V i∈Wallet G)(he:F∈Wallet G) :
    Cabin p (Φ t) μ F (∑ i∈S,V i)=∑ i∈S,Cabin p (Φ t) μ F (V i):= by
    induction S using Finset.induction with| empty=> simp only [Finset.sum_empty]; unfold Cabin; funext w; rw [scatter_congr _ _ _ (fun _ _=>(0:ℂ)) ?_]; exact map_zero (allocate ..); intro _ _ _; simp [meshZ]| insert i s hi ih=> have hx j hj:= h j ( Finset.mem_insert_of_mem ( b:=i ) hj ); rw [Finset.sum_insert hi, Finset.sum_insert hi, mark_sum2 t p ( h _ (by simp) ) ( Submodule.sum_mem _ hx ) he, ih hx ]
lemma mark_quote {U':TreeLine.Line G}(c d:ℂ): Cabin p U' μ (c • F) (d • H)= c • d • Cabin p U' μ F H:= by
    unfold Cabin; let q(i j:ℂ):= c*(d*(i*j)); funext w; simp only [Pi.smul_apply,smul_eq_mul]
    let P:=allocate (field ( Landau.parity (A:=Axis) (C:=G.ColorIndex))) w (R:=ℂ)
    change P _=c • d • P _; rw [ ← map_smul,← map_smul ]; apply scatter_congr; intro l r _; simp only [Pi.smul_apply, smul_eq_mul];
    have H' i j (v:QP): meshZ U' i j (c • F) (d • H) l r v=c*(d*meshZ U' i j F H l r v):= by unfold meshZ; simp only [Pi.smul_apply,smul_eq_mul]; ring
    simp_rw [ H', mul_left_comm (Tone.bill p _) c, mul_left_comm (Tone.bill p _) d, integral_const_mul, ← Finset.mul_sum ]; ring
end calculus

local notation "B" => Press.portDeck G
variable {K: Land.Booked (Press.portDeck G)} (M:MS_Data G K)
local notation "J" => MarkRows.I (Press.portDeck G)
def mark (i:J) : Rake.Label B:= ⟨4, address i⟩
def roster (i j:J): Fin 2→ Rake.Label B:= ![mark i,mark j]
local notation "a" => Finset.univ (α:=Fin 2)
variable (x:Fin 2 →QP) (hx:Injective x)
def pulse (i j:J)(n:ℕ): Reading G:= fun s t=> Dial.spine M (roster i j) s.1 x a n () s.2 t
def read (Z:J→ℝ)(n:ℕ): Reading G:= ∑ i:J, ∑ j:J,(Z i:ℂ) • (Z j:ℂ) • pulse M x i j n
local notation "η" => Energy.called 1 2 G
local notation "U" => read M x η
local notation "Hκ" => MarkRows.packet M η
local notation "Sμ" => Archive 4 M.bulk
local notation "R0" => x 1-x 0

abbrev pack_source (p:QP)(X : ℕ → Reading G)(Y:ℕ→Reading G)(n:ℕ) (s:Clock ℝ) : Law G:=
    ∑ i∈ antidiagonal n, Cabin p (PlanetD G s.2) ( covMeasure Axis ) ( X i.1 s ) ( Y i.2 s )
-- warning Cabin orientation last (X? choose Y). derive
def queue (M:MS_Data G K)(Q:ℕ→ Reading G) (n:ℕ) (s:Clock ℝ) : Law G:=
      ∑ i∈Domain.paths n 0, tree parity (PlanetD G s.2) ( Archive 4 M.bulk (n-i) s ) ( Q i s )
def source (n:ℕ)(s:Clock ℝ) : Law G := queue M U n s + pack_source (R0) Hκ Hκ n s
def triggerP (n:ℕ)(s:Clock ℝ) := cycle (Φ s.2) μ (U n s) + source M x n s

/- min picks etc choose orientation maybe define pack α count opposite -/
include hx
lemma weight_pulse (i j:J)(n:ℕ)(s:Clock ℝ) :
    let V:= Dial.spine M (roster i j) s.1 x
    let X:=Rake.approach ( Tide.frameF Unit s.1 ) M
    let L:=constantP G Unit (Φ)
    Vane.rhs (fun p (_:Unit)=>x p) (fun (_:Unit)=>μ) L L X V a n () s.2=
        cycle (Φ s.2) μ ( pulse M x i j n s ) + queue M ( pulse M x i j ) n s +
          pack_source (R0) ( ear M (address j) ) ( ear M (address i) ) n s:= by
    intro V X L; unfold Vane.rhs Vane.Src multi; -- binder
    unfold V; have hp:= Dial.pin M (roster i j) s.1 hx; rw [ show picks a={{1}} from rfl, Finset.sum_singleton,
         show a\{1}={0} from rfl, hp.2.1, hp.2.1 ];
    simp only [Rake.lonely, regionC, Pi.add_apply, Finset.sum_apply ]; rw [add_assoc]; apply congr_arg₂ (· + ·) rfl; unfold queue pack_source; apply congr_arg₂ (· + ·) rfl; -- need values defeq
    have H: (( rootX (I:=Unit) (fun p _=> x p) {1} () )- rootX (I:=Unit) (fun p _=>x p) a ())= x 1-x 0:= by rw [rootX,dif_pos (Finset.singleton_nonempty _),rootX,dif_pos Finset.univ_nonempty,min'_singleton ]; rfl
    simp_rw [ Pi.sub_apply,H ]; rfl

lemma tail_goal (t:ℝ): Rake.Mesh ( Tide.frameF Unit t ) ( fun p (_:Unit)=> x p ):= by intro i j hij; have hz : 0<‖x i-x j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (hx.ne hij)); exact ⟨⟨ _,hz,fun _=>by simp [Tide.frameF, Geo.roots] ⟩,⟨ _,hz,fun _=>by simp [Tide.frameF, Geo.roots] ⟩⟩

lemma afford (i j:J)(S:Finset (Fin 2))(hs:S.Nonempty)(n:ℕ)(s:Clock ℝ) :
     let Y:= Dial.spine M (roster i j) s.1 x
     Y S n () s.2∈ Wallet G:= by
   intro Y
   exact Wallet.awake ( Vane.founded (builder M (tail_goal x hx _) (roster i j)) ( Dial.pin M _ _ hx ) hs n|>.2 ) () s.2
lemma spool (i j:J)(n:ℕ)(s:Clock ℝ): pulse M x i j n s ∈ Wallet G:= afford M x hx i j _ univ_nonempty n s
omit hx
lemma stock (i:J)(n:ℕ)(s:Clock ℝ): ear M (address i) n s ∈Wallet G:=by -- Pages
   have hv:=(markView M (address i) n|>.host)
   refine Breeze.permits.mpr (fun E _ _ w=>?_); rw [Breeze.spaceArc]; exact Outlook.BigG (hp:=( blade0 (s:=s.2) (y:=s.1) hv ).price ) 0 w
lemma wallet_marker (e:ℕ)(s:Clock ℝ): Hκ e s∈ Wallet G:= by rw [MarkRows.own]; exact Submodule.sum_mem _ fun j _=> Submodule.smul_mem _ _ (stock M j e s)
lemma single_meshE (e:ℕ)(s:Clock ℝ)(v:QP):
    pack_source v Hκ Hκ e s= ∑ i:J,∑ j:J,(η i:ℂ) •(η j:ℂ) • pack_source v (ear M (address j)) (ear M (address i)) e s:= by
    have h(t): ∀ r:ℕ, Cabin v (Φ s.2) μ ( Hκ t s ) ( Hκ r s )=∑ i:J,∑ j:J,(η i:ℂ) •(η j:ℂ) • Cabin v (Φ s.2) μ (ear M (address j) t s) (ear M (address i) r s):= by
       intro r; have he i n: (η i:ℂ) • ear M (address i) n s∈Wallet G:= Submodule.smul_mem _ _ ( stock M i n s );
       conv_lhs => arg 5; rw [MarkRows.own]
       rw [mark_finR s.2 v _ (fun j _=> he j _) (wallet_marker M t s)]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [ MarkRows.own,mark_finL s.2 v _ (fun j _=> he j _) ( he i _ ) ]; exact Finset.sum_congr rfl fun j _=> (mark_quote v _ _).trans (smul_comm _ _ _)
    unfold pack_source; simp_rw [ h,Finset.smul_sum ]; rw [ Finset.sum_comm ]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_comm )
include hx
lemma afford_E (n:ℕ)(s:Clock ℝ): U n s ∈Wallet G:= by
    unfold PhasePair.read; simp only [ Finset.sum_apply,Pi.smul_apply ]; exact Submodule.sum_mem _ fun i _=> Submodule.sum_mem _ fun j _=> Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (spool M x hx i j n s))
lemma clock_source (n:ℕ)(s:Clock ℝ): triggerP M x n s =∑ i:J,∑ j:J,(η i:ℂ) • (η j:ℂ) • Vane.rhs (fun p (_:Unit)=> x p) (fun _=> planeF)
   ( constantP G Unit (Φ)) (constantP G Unit (Φ)) ( approach ( Tide.frameF Unit s.1 ) M ) ( Dial.spine M (roster i j) s.1 x ) a n () s.2:= by
     have he(e): U e s=∑ i:J,∑ j:J,(η i:ℂ) •(η j:ℂ) • pulse M x i j e s:= by unfold PhasePair.read; simp only [ Finset.sum_apply,Pi.smul_apply ]
     let Cq(l:Law G):= cycle (Φ s.2) μ l
     let P:=deep G s.2; have hF: Cq (U n s)= P ( U n s ):=( Breeze.weightC ( afford_E M x hx n s ) .. ).symm
     have hm i j:Cq (pulse M x i j n s)= P ( pulse M x i j n s ):= ( Breeze.weightC ( spool M x hx i j n s ) .. ).symm
     have center: queue M U n s=∑ i:J,∑ j:J,(η i:ℂ) •(η j:ℂ) • queue M (pulse M x i j) n s:= by
        unfold queue; simp_rw [ he, ←blvd,map_sum,map_smul,Finset.smul_sum ]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _=>Finset.sum_comm)
     unfold triggerP source; unfold Cq at hm hF; rw [center,hF,single_meshE]; simp_rw [he, map_sum, map_smul,planeF, weight_pulse M x hx, hm, smul_add,Finset.sum_add_distrib, add_assoc ]

lemma pace_E (n:ℕ)(s:Clock ℝ)(w:Legs (Lane4 G)) : HasDerivAt (fun t:ℝ=>U n (s.1,t) w) ( triggerP M x n s w ) s.2:= by
    rw [ clock_source M x hx ]; unfold PhasePair.read pulse; simp only [ Finset.sum_apply, Pi.smul_apply ]; refine HasDerivAt.fun_sum fun i hi=> HasDerivAt.fun_sum fun j hj=>?_ ; exact (( ( Vane.motion (builder M (tail_goal x hx s.1) (roster i j)) ( Dial.pin M (roster i j) s.1 hx ) Finset.univ_nonempty n ).pace () w (fun i=>Bool.noConfusion i) s.2 ).const_smul ( (η j):ℂ ) ).const_smul (η i:ℂ)
lemma provisional (n:ℕ)(w:Legs (Lane4 G))(t:ℝ): Tendsto (fun u:ℝ=> U n (t,u) w) atBot (𝓝 0) := by
    have he i j : Tendsto (fun u:ℝ=>pulse M x i j n (t,u) w) atBot (𝓝 0):= by
        let V:= Dial.spine M (roster i j) t x; obtain ⟨_,_,hW⟩:= (Dial.pin M _ _ hx).2.2 a (by simp) n
        unfold pulse; dsimp only; rw [ hW ]; unfold river; exact tendsto_integral_Iic_zero tendsto_id
    unfold PhasePair.read; simp only [Finset.sum_apply,Pi.smul_apply]; have ht(i j:J) := (( he i j ).const_smul (η j:ℂ)).const_smul (η i:ℂ)
    simpa only [smul_zero, Finset.sum_const_zero] using ( tendsto_finsetSum Finset.univ (fun i _=> tendsto_finsetSum Finset.univ (fun j _=> ht i j) ) )
omit hx in
abbrev sale_at (t:ℝ)(n:ℕ) := ∑ i:J,∑ j:J,(η i:ℂ)*(η j:ℂ)* Dial.book M (roster i j) t x a n
lemma IR (n:ℕ)(t:ℝ) : Tendsto (fun u:ℝ=> U n (t,u) [] ) atTop (𝓝 (sale_at M x t n)):= by
    have he(i j:J): Tendsto (fun u:ℝ=>pulse M x i j n (t,u) []) atTop (𝓝 (Dial.book M (roster i j) t x a n)):= ( ( Dial.reports (roster i j) (tail_goal x hx t) ( Dial.pin M _ _ hx ) Finset.univ_nonempty n ).1 () )
    unfold PhasePair.read sale_at; simp only [ Finset.sum_apply,Pi.smul_apply,smul_eq_mul, mul_assoc ]; exact tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ (fun j _=> ( (he i j).const_mul _ ).const_mul _))
lemma bag (n:ℕ)(t:ℝ): ∃ k:ℕ,∀ s:ℝ,∀ w:Legs (Lane4 G), k<w.length → U n (t,s) w=0:= by
    have hp(i j:J): ∃ k:ℕ,∀ s w,k<List.length w→pulse M x i j n (t,s) w=0:= by obtain ⟨k,he⟩:= ( Vane.founded (builder M (tail_goal x hx t) (roster i j)) ( Dial.pin M _ t hx ) ( s:=a ) Finset.univ_nonempty n ).1; exact ⟨ k,fun s w hx=> he () s w (by omega)⟩
    choose k hk using hp; let V(i:J):= ∑ j:J,k i j;
    refine ⟨∑ i:J,V i,fun s w h=>?_ ⟩; unfold PhasePair.read; simp only [Finset.sum_apply,Pi.smul_apply]; refine Finset.sum_eq_zero (fun i hi=> Finset.sum_eq_zero (fun j hj=>?_)); rw [ hk ]; simp; exact lt_of_le_of_lt ( le_trans (show k i j≤V i from by unfold V; exact Finset.single_le_sum (fun i _=> Nat.zero_le (k _ i)) hj ) (Finset.single_le_sum (fun i _=> Nat.zero_le (V i)) hi)) h
end
end YM.SignedWilsonExpansion.PhasePair
