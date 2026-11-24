import YM.FVAAlt2.Winder.Seed
/-! # Translation of the *same* input primitives commutes with leg-motion. Adapt
 Profiles.flavour_v until the many-operation. No quotient copying. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget.FVAAlt2.Wind.Seed
open Set Filter Function Layer Packet Tuple Oracle Lattice
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge} {P:ℕ} {q r m:ℕ}{X Y I J:Type}{n f c:Side}
lemma gradeRise (V:Equiv.Perm X)(F:Equiv.Perm I)(T:I→Micro X)(Q:I→ Orders X)(f:I→ℝ)(k:I→ℕ)
 (hp:∀ i,Lab (k i) (f i) (T i) (Q i))(he:∀ i t v,T (F i) t v=T i t (v∘V))(hf:∀ i,f (F i)= f i)(hh:∀ i,k (F i)=k i) (j q:ℕ)(i:I)(x:Tuple X q) : Q (F i) j q (V ∘ x)= Q i j q x:=by
 have hz(i e):(Q (F i)) e=fun r=>echo V (Q i e r):=by
    have ha:= hp (F i);rw [hf,hh] at ha;have hb:=hp i
    cases Nat.eq_zero_or_pos e with
    | inl hy=> subst e; rw [ha.awake,hb.awake];rfl
    | inr ht=>
      refine guessed (ha.scope_ e) ?_ ?_ ?_ ?_
      · intro r h; exact hb.scope_ e r (fun h' => h (by dsimp only;rw [h',echo_zero]))
      · exact ha.smooth e
      · intro r; exact echo_sym (hb.smooth e r)
      intro x; rw [ha.figures x ht,show flank (T (F i)) x=flank (T i) (x∘ V) from funext fun t=>he i t (t • x), ← hb.figures (x ∘ V) ht]; apply Finset.sum_congr rfl; intro j _; dsimp only
      rw [strum_perm x V]; rw [show (fun z: Tuple X j=> echo V (Q i e j) (V ∘ z))=Q i e j from funext (echos _ _)]
 rw [ hz ]; exact echos ..
abbrev hibern (n:Side)(A:Type): Travel (Cover × A) (Site n × A):= Travel.march n (groundM A)
abbrev leave (n:Side)(G:Gauge):= Travel.march n (linksQ G)
lemma carry_g (h:Cover): (linksQ G).shiftB h= Halo.carryX h:= by
 ext1 i; rw [site_roll]; rfl
lemma steps (h:Cover): (leave n G).hop h=Halo.carryX (n.val • h):= carry_g .. -- namespace?
lemma tickets (n:Side)(T:Binding.Scale) {Q:Lattice.Face ℤ → Orders (Foot G)} (h:Prim.Plane T G Q) (e q:ℕ): Powered (leave n G) (hibern n PlaqAxes) (fun i=> Q i e q):=by
 intro z; let V:=n.val • z; have h' :=gradeRise (Halo.carryX (G:=G) V) ( (hibern n PlaqAxes).hop z ) (plain T G) Q (fun _=> -1) (fun _=> 2) h ?_ (fun _=>rfl) (fun _=>rfl) e q
 · intro i x; change Q _ e q _=Q _ e q _; rw [steps]; exact h' i x
 intro i t v; unfold plain; change T.beta t* G.price (faceValue (win G v) (plateTrans V i))= _
 rw [← carrier]; have h:= Face.send_price (win G v) i 1 V G.price G.price_inv fun x g=> G.price_conj ..; rw [summer_dir,pull_one] at h; rw [h]
abbrev Bump(f c:Side) := (hibern f Axis).disj (hibern c Axis)
lemma binding (S:StepData c f)(z:Cover): ((leave f G).disj (leave c G)).hop z= Profiles.bundleS S (c.val • z) := by
 change Equiv.sumCongr _ _=_; rw [ steps,steps ]; unfold Profiles.bundleS Profiles.strideR; rw [smul_smul, S.sizes, Nat.mul_comm c.val]
lemma armour (S:StepData c f)(z:Cover)(i:Edge Cover): (Bump f c).hop z (Sum.inl i) = Sum.inl (dis (Profiles.strideR S (c.val • z)) i):= by unfold Profiles.strideR; rw [smul_smul,Nat.mul_comm, ← S.sizes]; rfl
lemma fuel (S:StepData c f)(R:Binding.Scale)(T:Branchix→Orders (KFoot G))(h: Sphere S (Halo.bios S) R T)(i q:ℕ) : Powered ((leave f G).disj (leave c G)) ( Bump f c ) fun v=> T v i q:=by
 intro z; let p:= c.val • z
 have hm : ∀ x t v, prism S ( Halo.bios S ) R ( ( Bump f c ).hop z x ) t v=prism S ( Halo.bios S ) R x t (v ∘ Profiles.bundleS S p (G:=G)):=by
    rintro (x|x) t v
    · rw [armour S]; change carnal S (bios S) (dis (Profiles.strideR S p) x) t v=carnal S (bios S) x t (v ∘ bundleS S p); rw [carnal,carnal,Profiles.branch_path]; rfl
    change opi S _ (dis p x) t v=opi S _ x t _; unfold opi
    change _* G.price (win G (v ∘ Sum.inr) _ * _) =_* G.price (win G ((v ∘ Sum.inr) ∘ carryX p) _ * (pond _ _ (win G ((v ∘ Sum.inl) ∘ carryX _)) _)⁻¹)
    rw [← carrier,← carrier, strideR,pulled (S:=S)]; simp only [dis, translate]; rw [add_comm x.1]
 intro a b; rw [binding S]; exact gradeRise _ _ _ _ _ _ h hm (fun x=> by cases x <;> rfl) (fun x=>by cases x <;> rfl) i q a b -- hm compile
end YM.RegulatorIR.Budget.FVAAlt2.Wind.Seed
