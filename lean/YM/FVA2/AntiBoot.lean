import YM.FVA2.AntiFlats
/-!
# Mark seeds specifically in whole Gallery. $p(g)=J_0(-1)^{r}p(-g)$
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace YM.MS.Reed
open Filter Topology Set Function MeasureTheory Finset
open Plane Lifting Landau Landau.Detect Koszul Book Book.Convolve Book.Program Dock
open Pearl Train Outlook Mach Arts Arts.Spin Halo Arc Garment Hem Rock Rock.Path Alps Rock.Oceans
open Plane.Wire Arts.Pilot Color Flux Shine Hem.Mell Garment.Wick Motif Motif.Literal
open scoped Topology Classical ContDiff
variable {G:Gauge}{n d m h:ℕ}{z:ℂ}
local notation "ζ"=> J ( Shore G n ) ℂ
section boots
lemma leaf_J {C:Type*}{F:Raw C ℂ}(he:Book.rank 1 F): J _ ℂ F= -F := by ext l; by_cases hx:l.length=1; simp only [rite,hx,ϕ,pow_one,neg_one_mul]; rfl; rw [rite, Pi.neg_apply, he l (by rw [mod_int]; omega),mul_zero,neg_zero]
lemma squareζ (F H:Mield G n)(j:G.ColorIndex) : ζ ( jaw G n F H j )= jaw G n ((J _ ℂ) ∘ F) (( J _ ℂ )∘ H ) j:= by simp only [ chew,map_sum,map_smul,vertex ]; rfl
lemma poly_2 {F H:Mield G n}(hp:∀ j,ζ ( F j) = -(F j))(hx:∀ j,ζ (H j)= -(H j))(i:G.ColorIndex): ζ (jaw G n F H i)= jaw G n F H i:= by
   rw [squareζ,show (( J _ ℂ ) ∘ F) = -F from funext hp, show (( J _ ℂ ) ∘ H) = -H from funext hx, map_neg,map_neg,LinearMap.neg_apply, neg_neg ]
private lemma lead (i:Arts.L n) (j:G.ColorIndex): ζ (A n G i j) = -( A n G i j ):= leaf_J (mon_leaf _)
private lemma civil (j:G.ColorIndex): ζ ( cwave n G j )= -( cwave n G j ):= leaf_J (mon_leaf _)
private lemma nozzle (i j:Arts.L n)(c:G.ColorIndex): ζ ( quill i j c)=quill i j c:= poly_2 ( lead i ) ( lead j ) _
private lemma fork (i j:Arts.L n)(c:G.ColorIndex): ζ ( F₀ i j c)= -( F₀ i j c):= leaf_J (rank_α i j c)
private lemma channel (i:Chan G n): ζ (blazeV G n i)= blazeV G n i:= by
    rcases i with ⟨_|i,j⟩; · simp only [blazeV,Sc, Pi.smul_apply,map_smul,poly_2 civil civil ]; -- simp
    exact poly_2 (lead i) civil j
lemma spark (G:Gauge) : χ G ( Motif.B₁ G )= -(B₁ G):= by
    funext i; change J _ ℂ _ = _; unfold B₁ top3 cape sume; simp only [map_sum,map_add,map_smul,Motif.bite, vertex,Pi.neg_apply, channel,fork,nozzle, show ∀ a:Cfield G i, J _ ℂ (Motif.leaf a)= -(Motif.leaf a) from fun a=> leaf_J (mon_leaf a),map_neg,LinearMap.neg_apply, smul_neg,← neg_add, Finset.sum_neg_distrib ] -- check bite ns
lemma procyon (G:Gauge): χ G (B₂ G)=B₂ G:= by
    funext i; change J _ ℂ _=_; unfold B₂ top4 sume; simp only [ map_sum,map_smul,Motif.bite,vertex,nozzle ]
lemma chews (G:Gauge)(i:ℕ) : χ G (pulseX G i)= (ϕ i:ℂ) • pulseX G i:= by
   rcases i with _|(_|(_|i)); simp only [Up0,map_zero,smul_zero]; rw [pulse1,spark, ϕ,pow_one,neg_one_smul ]; rw [show pulseX G 2=B₂ G by simp [pulseX,Literal.hiss,Motif.χ],procyon]; simp [ϕ]; rw [show pulseX G (i+1+1+1)=0 by simp [pulseX, Literal.hiss,Motif.χ,Finsupp.single_eq_of_ne (show i+1+1+1≠2 from by omega)],map_zero, smul_zero]
lemma CorB (G: Gauge): νc 0 (Emit.gloss (pulseX G))= Emit.gloss (pulseX G):= by
    funext i t; change (ϕ (0+i):ℂ) • ( χ G (pulseX G i) )= pulseX G i; rw [zero_add,chews,smul_smul,invol,one_smul ]
end boots
section mark
private lemma sparkC (a b:Axis)(l:List Axis)(i:G.ColorIndex) : ζ ( Pole G n a b z l i )= -( Pole G n a b (-z) l i ):= by
   induction l generalizing i with
   | nil=> simp only [ Pole,cur,Pi.add_apply,Pi.smul_apply,map_add,map_smul,neg_smul, Pi.neg_apply, poly_2 ( lead (chair _ _) ) ( lead (chair _ _) ), fork,neg_add,neg_neg]
   | cons p l ih=>
     let S:= J ( Shore G n ) ℂ; let V:= Pole G n a b; let p':=chair n p;
     have hQ : (S ∘ V z l) = -( V (-z) l ):= funext ih; have hm(F:Rack G n): ζ ( rowP p' F )= rowP p' ( ζ F ):= by funext i; rw [rowP,rite, moon,moon,rite,mul_left_comm ] -- rowP maybe operator mapping 
     unfold Pole convoke; simp only [ LinearMap.add_apply,LinearMap.smul_apply,Pi.smul_apply,Pi.add_apply ]; unfold V S at hQ; rw [map_add,map_smul,squareζ,hQ,show ((( J _ ℂ ) ∘ A n G (chair n p))) = -A n G (chair n p) from funext (lead p'), map_neg,map_neg,LinearMap.neg_apply,neg_neg,neg_smul, axisP,lock ]; rw [ hm, ih ]; simp only [p',lock, map_neg,neg_add, neg_neg ]
lemma Jwing (m:ℕ)(f:Fin m→ Plaq)(σ:Lifting.Grid G m) : χ G ( Pole.wing m f σ z)= (ϕ m:ℂ) • Pole.wing m f σ (-z):= by
    funext i; induction m with
    | zero=> ext l; change J _ ℂ (coin 1) l=_; rw [rite ]; rcases l with _|⟨a,l⟩; simp only [ϕ,Pole.wing,List.length_nil,pow_zero,one_mul,one_smul]; rfl; simp [coin ]; rfl -- ugliness
    | succ k ih=> let J:=Pole.wing k (f∘Fin.succ) (σ ∘ Fin.succ); change Reed.J _ ℂ ( bite i G _ (J z i))=_; rw [ vertex ]; rw [show Reed.J _ ℂ (Pole_leaf (n:=i) z (f 0) (σ 0))=_ from sparkC ..,show Reed.J _ ℂ (J z i)=(ϕ k:ℂ) • J (-z) i from ih _ _ ]; rw [map_smul,map_neg,LinearMap.neg_apply, smul_neg,rite1,neg_smul ]; rfl
lemma ward_color (m:ℕ)(f:Fin m→Plaq)(σ:Lifting.Grid G m): χ G ( Pole.saint m f σ z)= (ϕ m:ℂ) • Pole.saint m f σ (-z):= by unfold Pole.saint; rw [ map_sum, Finset.smul_sum ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul,Jwing,smul_comm ]
lemma reception (F:ℂ→Mob G)(he:F ∈ Mach.Gallery G m n)(z:ℂ): χ G (F z)= (ϕ m:ℂ) • F (-z):= by
   refine Submodule.span_induction (p:=fun F _=> χ G ( F z )= (ϕ m:ℂ) • F (-z)) ?_ ?_ ?_ ?_ he
   · rintro f ⟨a,x,h,rfl⟩; exact ward_color m a x
   · rw [Pi.zero_apply,map_zero,Pi.zero_apply,smul_zero]
   · intro f g _ _ hf hg; rw [Pi.add_apply,map_add, Pi.add_apply,hf,hg,smul_add ]
   intro c f _ hx; change χ G ((c:ℂ) • f z)=(ϕ m:ℂ) • ((c:ℂ) • f (-z)); rw [map_smul,hx,smul_comm ]
-- presence at X≠due p explanation
end mark
section matchJ
open Land
variable {E:Type}[AddCommGroup E][Module ℂ E]{d:ℕ}{X Y: Box (Mob G)}{p: Law G}
private def film (E:Type)[AddCommGroup E][Module ℂ E]: Box E →ₗ[ℂ] Box E:= Finsupp.lsum ℂ fun i:ℕ=> (ϕ i:ℂ) • ( Finsupp.lsingle i )
private lemma film_sl (i:ℕ)(x:E): film E (.single i x)= (ϕ i:ℂ) • .single i x:= Finsupp.lsum_single ..
private lemma film_h (x:Box E)(n:ℕ): film E x n=(ϕ n:ℂ) • x n:= by
   induction x using Finsupp.induction_linear with
   | zero=> simp
   | single a v=>
       rw [film_sl, Finsupp.smul_apply]; by_cases ha:n=a; · rw [ha]
       simp [Finsupp.single_eq_of_ne ha]
   | add a b ha hb=> rw [map_add, Finsupp.add_apply, Finsupp.add_apply,ha,hb,smul_add]
private lemma film_v (x:Box E)(z:ℂ): value E z ( film E x)=value E (-z) x:= by
   induction x using Finsupp.induction_linear with
   | zero=> simp
   | single a v=> rw [film_sl,map_smul,value_sl,value_sl, smul_smul,ϕ,← mul_pow,neg_one_mul ]
   | add a b ha hb=> rw [map_add,map_add,map_add,ha,hb]
private lemma faceV (he:∀ z:ℂ,value (Mob G) z X=value (Mob G) z Y): X=Y:= by
    ext n w l; apply sub_eq_zero.mp; exact valuedZ ( X-Y ) (Garment.Wave.slice l) (fun i=> by rw [ map_sub, he,sub_self,map_zero ]) n -- namespace
lemma optic_leaf (hx:Ele h m p X): νc m (Emit.gloss (linear (Mob G) X))=Emit.gloss (linear (Mob G) X):= by
   let M:= Mob G; let f:=film M X; let Q:=ϕ (R:=ℂ); let U:=Boom 0 (χ G) X; have hp:U= Q m • f:= faceV fun i=> by rw [linear_v,map_smul,film_v]; exact reception _ hx.1 i
   have he n: χ G ( X n )= Q (m+n) • X n:= by rw [ ← whole (χ G) X, show Boom _ _ _= _ from hp,hiss,Finsupp.smul_apply, show f n = _ from film_h X n,smul_smul ]; change (((-1:ℂ)^m)*((-1)^n)) • X n=(-1:ℂ)^(m+n) • X n; rw [pow_add ]
   funext n z; change Q (m+n) • ( χ G ( X n ) )= X n; rw [he, smul_smul,invol,one_smul ]
-- continuation obeys parity
variable {B: Local.Physical.Deck G}{O: Booked B}(K: MS_Data G O)
lemma leaderJ : leader G (νp 0 K.bulk) (Emit.gloss (pulseX G)) (νc 0 K.poleS):= CorB G ▸ stands K.bulkOK -- syntax rw stuck eliminator?
lemma poleB : νc 0 K.poleS= K.poleS ∧ ∀ i,Pact (νp 0 K.bulk i) (K.bulk i):= unique_B ( leaderJ K ) K.bulkOK
lemma cometJ (i:Land.Plaid B h): comet h 0 (νp 0 K.bulk) ( Emit.gloss ( linear ( Mob G ) ( O.optics h i ))) ( νp ( Land.read i ).grade ( K.marks h i ) ) ( νc ( Land.read i ).grade (K.poles h i) ):= optic_leaf ( O.law h i ) ▸ runsJ ( Land.read i ).grade ( K.markOK h i )
lemma poleM (i:Land.Plaid B h): νc (Land.read i).grade (K.poles h i)=K.poles h i ∧ ∀ n,Pact (νp (Land.read i).grade ( K.marks h i ) n) (K.marks h i n):= unique_M ( cometJ K i ) (K.markOK h i) (poleB K).2
lemma powerRoad {F: T (Flats G)}(hp:∀ i,Pact (νp m F i) (F i))(he:∀ i,Stay h ( F i ))(ht:∀ i, Stay h ( νp m F i )) (x:ℝ×ℝ)(n:ℕ): Archive h F n x=(ϕ (m+n):ℂ) • J _ ℂ ( Archive h F n x ):= by
   obtain ⟨x,y⟩:=x; let t:= (ϕ (m+n):ℂ); have h:hereZ h (νp m F n) y x=t • χ G ( hereZ h (F n) y x):= by
       apply Lift.unique (live0 (ht n)); rw [νp,page_smul, ← buys ]; exact Lift.static ( loop_mer ( live0 ( he n ) ) ) _
   conv_lhs=> rw [← FVA2.ArchTurn.archive_h hp ht he]
   change hereZ _ _ y x 0=_; rw [ h ]; rfl
lemma ArchiveJ : ∀ n t, Outlook.Archive 4 K.bulk n t=(ϕ n:ℂ) • J _ ℂ (Outlook.Archive 4 K.bulk n t) := by
   intro n t; simpa only [zero_add] using powerRoad (G:=G) (h:=4) (poleB K).2 (fun i=> ( Dock.gang (K.bulkOK i) ).dost) (fun i=> (gang ( leaderJ K i )).dost) t n -- exact maybe not exact_mod
lemma sale_archive (i: Land.Plaid B h)(n:ℕ) (t:ℝ×ℝ): Archive h (K.marks h i) n t=(ϕ ((Land.read i).grade+n):ℂ) • J _ ℂ ( Archive h (K.marks h i) n t ):= powerRoad (poleM K i).2 (fun j=> (gang (K.markOK h i j)|>.dost)) (fun j=>(gang (cometJ K i j)|>.dost)) t n
end matchJ
end YM.MS.Reed
