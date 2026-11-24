import YM.FVA2.PolarOptics
/-!
# Physical compatible averaged MS continuation

The optic choice only. Entire Laurent procedure is then applied as is.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace YM.FVA2.ArchTurn
open Filter Topology Set Function MeasureTheory MS MS.Logarithm MS.Land
open MS.Plane MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Convolve MS.Book.Program MS.Dock
open MS.Pearl MS.Train MS.Outlook MS.Mach MS.Arts MS.Arts.Spin MS.Halo MS.Arc MS.Garment MS.Hem MS.Rock MS.Rock.Path MS.Alps
open MS.Plane.Wire MS.Arts.Pilot MS.Rock.Oceans MS.Color MS.Shine MS.Hem.Mell ColorCode MS.SpinCode
open MS.Motif MS.Motif.Literal
open scoped Topology Classical ContDiff
variable {G: Gauge} (M:Booked (wings G))(V:Warehouse G) (s:Signed) {m n h:ℕ}
abbrev Owner (G:Gauge)(d:ℕ):= MS.Land.Plaid (wings G) d
variable (i j:Owner G h)
def pactV (i:Owner G h) : Box (Mob G) := polar s (∑ j: Owner G h, (ColorCode.fee V.F s.ortho h i j:ℂ) • M.optics h j)
def angular : Booked (wings G) where
   optics h i := ∑ s:Signed,(↑(Fintype.card Signed):ℂ)⁻¹ • pactV M V s i
   law h i:= by
       have he {h:ℕ} {L Q: Box (Mob G)}{H K:Law G}(hp:Ele h (Land.read i).grade H L)(hx: Ele h (Land.read i).grade K Q) : Ele h ( Land.read i ).grade (H+K) (L+Q):= by
           refine ⟨ ?_,?_⟩; simp_rw [ map_add ]; exact Submodule.add_mem _ hp.1 hx.1; rw [ Finsupp.add_apply,Pi.add_apply, hp.2,hx.2 ]
       let t:= (Land.read i ); let c:= (↑(Fintype.card Signed):ℝ);
       have zc: ((c⁻¹ :ℝ):ℂ)=(↑(Fintype.card Signed):ℂ)⁻¹:= by unfold c; push_cast; rfl
       have hz: Ele (G:=G) h t.grade 0 0 := ⟨ show (fun z=> value (Mob G) z 0)∈ Gallery G (t.grade) h from (by simp only [map_zero ]; exact Submodule.zero_mem _), rfl⟩
       have ht (s:ℝ) {X: Box (Mob G)} {F: Law G} (hi : Ele h t.grade F X) : Ele h t.grade ((s:ℂ) • F) ((s:ℂ) • X):= by refine ⟨ ?_, ?_ ⟩; simp_rw [ map_smul ]; exact ( Gallery G t.grade h ).smul_mem s hi.1; rw [Finsupp.smul_apply,Pi.smul_apply,hi.2 ]
       have hu {A:Type}(x:Finset A){F:A→ Law G}{g:A→Box (Mob G)}(H:∀ i∈x,Ele h t.grade (F i) (g i)): Ele h t.grade (∑ i∈x,F i) (∑ i∈x,g i):= by classical induction x using Finset.induction with| empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact hz| insert i x hi ih=> rw [ Finset.sum_insert hi,Finset.sum_insert hi]; exact he (H i (by simp)) ( ih (fun t h=> H _ (Finset.mem_insert_of_mem h)))
       have hp (s:Signed): Ele h t.grade t.read (pactV M V s i):= by
           obtain he:= height_c s V i; have h0:t.read= backlit s _:= Eq.trans ( Eq.symm ( show backlit s ( backlit s⁻¹ t.read )= _ from by nth_rw 1 [← inv_inv s]; exact shift_back s⁻¹ t.read )) (congr_arg _ he); rw [h0]; refine raises s (hu _ (fun j _ =>?_)); by_cases hp:t.grade=(Land.read j).grade; exact ht _ (hp.symm ▸ (M.law h j))
           rw [ ColorCode.fee,held_real,shown_off _ _ _ _ _ (fun h=> hp (congr_arg Prod.snd h)),zero_smul,zero_smul]; exact hz
       simp_rw [ ← zc ]; have hh : ∑ _x:Signed, (↑(c⁻¹):ℂ) • t.read=t.read:= by rw [ ← Finset.sum_smul, Finset.sum_const, Finset.card_univ,nsmul_eq_mul,zc,mul_inv_cancel₀ ( by exact_mod_cast Fintype.card_pos (α:=Signed)|>.ne'),one_smul]
       exact hh ▸ hu Finset.univ (fun s _=> ht _ (hp s)) -- may in other positions
lemma lit : polar s⁻¹ ((angular M V).optics h i)= ∑ j:Owner G h, ( ColorCode.fee V.F s.ortho h i j:ℂ) • (angular M V).optics h j:= by
   let φ:= V.F; let D(q:Signed)(i j: Plaid (wings G) h):ℂ:= ColorCode.fee φ q.ortho h i j; have hu (k:Signed) : polar s⁻¹ (pactV M V k i) = ∑ j:Owner G h,D s i j • pactV M V (k*s⁻¹) j:= by
       unfold pactV; rw [polar_c, map_sum ]; simp_rw [ map_sum,map_smul, Finset.smul_sum, smul_smul ]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _;
       simp_rw [D, φ,← Complex.ofReal_mul,← Finset.sum_smul, ← Complex.ofReal_sum, ← ColorCode.fare_l ]; congr 3; change Signed.inclusionO _= Signed.inclusionO _* Signed.inclusionO _; simp
   unfold angular; rw [ map_sum ]; simp_rw [map_smul, hu, Finset.smul_sum ]; rw [ Finset.sum_comm ]; apply Finset.sum_congr rfl; intro j _; let f (u:Signed):= ( ↑(Fintype.card Signed):ℂ)⁻¹ • pactV M V u j;
   simp_rw [smul_comm _ (D s i j) ]; exact Equiv.sum_comp (Equiv.mulRight s⁻¹) (fun k=> D s i j • f k)
-- linearities
variable {f g c d:T (Coat G)}{X J Y:T ( Flats G)}  {u t:ℤ}
lemma comet_p (hf:comet h t X f J g)(he:comet h t X c Y d) : comet h t X (f+c) (J+Y) (g+d) := by
   intro i; obtain ⟨⟨n,H,hN,Q⟩,hV⟩:= hf i; obtain ⟨⟨m,H',hM,P⟩,hA⟩:= he i; refine ⟨⟨ max n m, ?_, Cap0.heap.plus (clockTrans hN (le_max_left n m)) (clockTrans hM (le_max_right n m)), (Q.collects (le_max_left n m)).add (P.collects (le_max_right n m)) ⟩,fun s=> False.elim s⟩; obtain hp := H.plus H'; simp only [ platform,map_add,Pi.add_apply,Finset.sum_add_distrib ]; convert hp using 1; unfold platform; abel
lemma comet_s (hf:comet h t X f J g)(k:ℝ) : comet h t X ((k:ℂ) • f) ((k:ℂ) • J) ((k:ℂ) • g):= by
   intro i; obtain ⟨⟨n,H,hN,Q⟩,hV⟩:= hf i; refine ⟨ ⟨n, ?_, fun i=> (hN i).smul (by simp), Q.smul (by simp)⟩,fun s=>False.elim s⟩; simpa only [ platform, Pi.smul_apply, Finset.smul_sum, map_smul, smul_add ] using H.scale (k:ℂ)
lemma comet_z {G: Gauge} {X:T ( Flats G )} : comet h t X 0 0 0:= by intro i; simp only [PathD,Pi.zero_apply,platform,map_zero,Finset.sum_const_zero]; exact zero_sing _ -- unpack Pi at arg ST
lemma comet_t {A:Type}(x:Finset A){F:A→ T (Coat G)}{g:A→ T (Flats G)}{W:A→T (Coat G)}(he:∀ i∈x,comet h t X (F i) (g i) (W i)): comet h t X (∑ i∈x,F i) (∑ i∈x,g i) (∑ i∈x,W i):= by classical induction x using Finset.induction with| empty=> rw [ Finset.sum_empty,Finset.sum_empty,Finset.sum_empty ]; exact comet_z| insert i x hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]; exact comet_p (he i (by simp)) ( ih (fun i hi=> he i (Finset.mem_insert_of_mem hi)))
lemma archive_h {F H: T (Flats G)}(hv:∀ i,Pact (F i) ( H i ))(he:∀ i,Stay h (F i))(ht:∀ i,Stay h (H i)): Archive h F=Archive h H:= by
    ext n x; obtain ⟨i,y⟩:= x; change hereZ h (F n) y i 0 _= _;
    rw [ Lift.unique ( live0 (he n)) (Lift.congr ( live0 (ht n) (s:=y) (y:=i)) (prom ( pact_sym ( hv n )) h y i)) ]; rfl -- trouble ext x l : Eta maybe
lemma overbook (A: MS_Data G (angular M V)) : Blaze.Turns V A := by
   constructor; intro s h i; let U:= A.marks h; let C (j:Owner G h):ℝ:= ColorCode.fee V.F s.ortho h i j; let B(j:Owner G h):= (angular M V).optics h j
   let Q (X:Box (Mob G)):= MS.Emit.gloss (Literal.linear (Mob G) X)
   have hp : comet h 0 A.bulk ( Q ( polar s⁻¹ (B i)) ) (fun n=> flatQ s⁻¹ (U i n)) (fun n=>tickW s⁻¹ (A.poles h i n)) := by
       convert comet_h s⁻¹ A.bulkOK (A.markOK h i) using 1; funext n z; exact whole .. 
   let u:= s⁻¹; let V' := ∑ j:Owner G h,(C j:ℂ) • U j
   have hc := comet_t Finset.univ (fun j _=> comet_s ( A.markOK h j ) (C j))
   -- turn its input to Q
   have hu : Q (polar s⁻¹ (B i))=∑ j:Owner G h,(C j:ℂ) • Q (B j):= by
       rw [show polar s⁻¹ (B i)= _ from lit M V s i]; unfold Q MS.Emit.gloss; rw [map_sum ]; simp_rw [map_smul ]; funext k z; simp only [ Finset.sum_apply, Pi.smul_apply ]; rfl
   unfold Q B at hu; rw [← hu] at hc
   obtain ⟨hS,hQ⟩:= unique_M hp hc (fun i _=> EventuallyEq.rfl); ext n x l; obtain ⟨i',y⟩:= x; change SpinCode.backlit s⁻¹ ( hereZ h (U i n) y i' 0 ) _= _; have he : hereZ h (flatQ u (U i n)) y i'= canto u ( hereZ h (U i n) y i'):= by
       apply Lift.unique ( live0 (Dock.gang ( hp n ) ).dost ); rw [ ← parade_h ]; exact limb u ( live0 ( Dock.gang ( A.markOK h i n ) ).dost )
   rw [ ← ceiling0 ]; change canto u (hereZ h (U i n) y i') 0 _= _; rw [← he]; have ξ := congr_fun (congr_fun (archive_h hQ (fun i=> ( Dock.gang ( hp i ) ).dost) (fun i=> ( Dock.gang ( hc i ) ).dost)) n ) (i',y); change hereZ h (flatQ u (U i n)) y i' 0= _ at ξ; rw [ξ]; -- linear Archive via Lift sums
   have hh: hereZ h (V' n) y i'=∑ j:Owner G h,(C j:ℂ) • hereZ h (U j n) y i':= by
       apply Lift.unique (live0 (Dock.gang (hc n)).dost); simp_rw [ Finset.sum_apply,Pi.smul_apply, page_sum,page_smul ]; exact ( show Pick 0 _ _ from Pick.fin _ (fun i _=> Lift.static (live0 (Dock.gang (A.markOK h i n)).dost) _))
   change hereZ h (V' n) y i' 0 l= _; rw [hh ]; simp_rw [ Finset.sum_apply,Pi.smul_apply ]; rfl
end YM.FVA2.ArchTurn
