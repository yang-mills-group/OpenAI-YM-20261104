import YM.FVA2.SteadyBooked
/-!
# Unit to all orders: in the stipulated interface with fitted real stencils
-/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.FVA2.Frost
open Filter Topology Set Function MeasureTheory MS MS.Logarithm MS.Land
open MS.Plane MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Convolve MS.Book.Program MS.Dock MS.Garment.Wick
open MS.Pearl MS.Train MS.Outlook MS.Mach MS.Arts MS.Halo MS.Arc MS.Garment MS.Hem MS.Rock MS.Rock.Path MS.Alps
open MS.Plane.Wire MS.Arts.Pilot MS.Rock.Oceans MS.Color MS.Shine MS.Hem.Mell ColorCode MS.SpinCode
open MS.Menus MS.Motif MS.Motif.Literal ArchTurn
open scoped Topology Classical ContDiff
variable {G:Gauge}(V:Warehouse G) (B:Booked (wings G)){m n:ℕ} (i: Owner G 0) (P:MS_Data G B)
local notation "R"=> Land.read i
abbrev oneI (i:Owner G 0): ℂ:= ( Land.read i ).read []
lemma tip0 (p: Glyph (wings G) 0): p.grade=0:= Nat.eq_zero_of_le_zero ( Glyph.memory p )
-- stencil fitted at arity zero from only constant $Label(0,0)=unit by rank$.
def pile (k:ℂ): Mob G:= fun _=> coin k
-- relationship Boss determines Σ choice
lemma king (K: Box (Mob G))(L: Law G)(he:Ele 0 0 L K): K= Finsupp.single 0 (pile (L [])) := by
   have hu : ∀ z:ℂ,value _ z K=pile (value _ 0 K 0 []) := by
       intro z; let S:= (fun z:ℂ=>value (Mob G) z K);
       refine Submodule.span_induction (p:=fun (f:Coat G) _=> f z=pile (f 0 0 [])) ?_ ?_ ?_ ?_ he.1
       · rintro u ⟨f,j,h,rfl⟩; unfold Pole.saint; ext i l; simp_rw [Finset.sum_apply ]; cases l with | nil=>rfl| cons i l=> exact Finset.sum_eq_zero fun i _=> mul_zero _ -- type mismatch
       · ext m l; cases l <;> rfl
       · intro f g _ _ hp ht; simp only [ Pi.add_apply ]; rw [hp,ht]; ext m l; cases l <;> simp [pile,coin]
       intro k f H hf; simp only [Pi.smul_apply,hf]; ext m l; cases l <;> simp [pile,coin]
   let A : Box (Mob G):= Finsupp.single 0 ( pile (L []) ); change K=A;
   apply sub_eq_zero.mp; ext n m l; let V: Mob G→ₗ[ℂ] ℂ:= Garment.Wave.slice l; -- context names
   change V ((K-A) n)=0; apply valuedZ (x:= K-A); intro z; rw [ map_sub (value ..), hu z, low_row, he.2 ]; unfold A; simp only [value_sl,pow_zero,one_smul,sub_self,map_zero]
lemma franc (i:Owner G 0) : (B.optics 0 i)= Finsupp.single 0 (pile (oneI i)):= by
   apply king _ (L:= (Land.read i).read); obtain he:= B.law 0 i; unfold Menus.Glyph.read at he; -- invalid subst due bit
   convert he using 2; exact (tip0 (Land.read i)).symm
-- nil Estimate
lemma pion (K:Mob G)(b:ℂ)(W:Rip G) : squad W K (pile b)=0 := by
   funext n l; change scatter _ l _=0; refine Eq.trans ( scatter_congr (field Landau.parity) l _ 0 (fun i j hi=>?_) ) (map_zero (allocate ..)); change Flux.attaches Landau.parity (W n) ( K n ) (coin b) _ _=0; unfold Flux.attaches; dsimp only; simp [coin]
private def f (n:ℕ): Coat G:= MS.Emit.gloss (Literal.linear (Mob G) (B.optics 0 i)) n
private def Φ (n:ℕ): Flats G:= Finsupp.single 0 (f B i n)
def leer (i:Owner G 0)(n:ℕ) : ℂ:= if n=0 then oneI i else 0
lemma leer_k (n:ℕ)(z:ℂ) : (f B i n) z=pile (leer i n):= by unfold f; rw [franc]; unfold MS.Emit.gloss; rw [ hiss, Finsupp.single_apply ]; unfold leer; by_cases h:n=0; simp [h]; rw [if_neg (Ne.symm h),if_neg h]; ext i l; cases l <;> rfl
private lemma badge (n:ℕ): Count (f B i n) 0 ∧ kPrice (pile (G:=G) (leer i n)) ∧ Cap0 false 0 0 (f B i n):= by
    have he : Badge false (f B i n) 0 0:= Ele.grows ( B.law 0 i ) n; rw [ funext (leer_k B i n)] at he ⊢; obtain ⟨H,hf,X⟩:= give (K:=pile _) he; exact ⟨he.born,H,X,Eventually.of_forall (fun _=>(show Issue 0 (pile (G:=G) _) from fun k l hl=> by cases l; simp at hl; rfl))⟩
lemma duel (X:T (Flats G))(n:ℕ): platform X n (Φ B i)=0:= by
   unfold platform; refine Finset.sum_eq_zero fun j _=>?_; unfold drive0; generalize X j.1=J; induction J using Finsupp.induction_linear with
   | zero=> rw [map_zero, LinearMap.zero_apply ]
   | add p q hp hq=> rw [map_add,LinearMap.add_apply,hp,hq,add_zero]
   | single k z=>
        let F:= tapeB (squad (A0 G 0)) z; rw [TreeN, explode,Finsupp.lsum_single ]; change blast k F _=_; rw [Φ,blast_sl ]; obtain he : F (f B i j.2)=0:= funext fun x=> by change squad (A0 G 0) (z x) (f B i j.2 x)=0; rw [leer_k,pion];
        rw [ he,Finsupp.single_zero ]
private lemma stars (n:ℕ)(s y:ℝ): Lift ( Parade (Φ B i n) 0 y s ) (pile (leer i n)):= by
    obtain ⟨hp,H,_⟩:= badge B i n; rw [ Φ,pureP _ hp, funext (leer_k B i n) ]; exact Lift.stays H
lemma census (n:ℕ)(s y:ℝ): hereZ 0 (Φ B i n) s y= pile (leer i n):= Lift.unique ( live0 (fun x y=>⟨_,stars B i n y x⟩) ) (stars ..)
lemma amber (J:T ( Flats G)) : comet 0 0 J ( Emit.gloss ( Literal.linear (Mob G) (B.optics 0 i) ) ) ( Φ B i ) 0:= by
   intro n; obtain ⟨he,H,hN⟩:= badge B i n;
   have hu: ClockD false 0 0 (Φ B i n):= Cap0.heap.single hN _; refine ⟨⟨0,?_,hu,Cap0.zero⟩,fun x=>False.elim x⟩; rw [duel, zero_add ]; let X:= Φ B i n;
   obtain hK: Live (f B i n):= by rw [funext (leer_k B i n)]; exact Live.stays H
   exact (joint_static he hK).via (pact_sym (pact0 ⟨(0:ℤ)-2,by omega, clockCap (mine hu (joint_static he hK).toll).eye⟩ ))
lemma archivE (i:Owner G 0)(n:ℕ) (s y:ℝ): Archive 0 (P.marks 0 i) n ( y,s )= coin (leer i n):= by
   obtain h:= P.markOK 0 i; let X:= amber B i P.bulk; obtain ⟨L,V⟩:= unique_M h X (fun _ _=> EventuallyEq.rfl); rw [ archive_h V (fun i=>Dock.gang (h i)|>.dost) (fun i=>Dock.gang (X i)|>.dost) ]; exact congr_fun (census B i n s y) 0
end YM.FVA2.Frost
