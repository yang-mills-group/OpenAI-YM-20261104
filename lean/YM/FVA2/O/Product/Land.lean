import YM.FVA2.O.Product.Gains
/-!
# Natural-power all-rows version
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Serve
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff
open scoped Topology ContDiff
variable {G:Gauge}{t:Bool}{O:Type}{I:Type}{U:Planet G I}{F X Y:T (Glade G I)}{B: Deck G}{K:Booked B}{M:MS_Data G K}{q:ℤ}{η:I→ℝ}
local notation "A"=> both G I
abbrev voyage (U: Planet G I)(b:Bool): Pair ( Glade G I ):= Puff.points I fun i=> Puff.points ℝ fun s=> crossF ( U i s ) b
abbrev hori (G:Gauge)(I:Type): Actors ( Glade G I ):= roof I ( roof ℝ ( Breeze.Shine G ) )
abbrev glaze (G:Gauge)(I:Type): Actors ( T (Glade G I) ):= (hori G I).stack SplitP.nat
lemma glazeV : F∈ (glaze G I).guard ↔ ∀ i j s,F i j s∈ Roof G:= by
    constructor; · exact fun h i j s=> h i (Set.mem_univ _) j (Set.mem_univ _) s ( Set.mem_univ _)
    exact fun h=> fun i _ j _ s _=> h i j s
lemma hedge (h:Banks X 0): X∈ (glaze G I).guard:= glazeV.mpr fun i u s=> ⟨( h i ).invoice,Ward.truthP ((h i).tone u s)⟩
lemma fixm (L:MH (Glade G I))(K:Pair (Glade G I))(h:∀ i j, L ( joint G I ( X i ) ( Y j ) )= joint G I (L (X i)) ( Y j )+joint G I ( X i ) ( L ( Y j ) )+ K ( X i ) ( Y j )) : promote L (bond G I X Y)=bond G I (promote L X) Y+bond G I X (promote L Y)+pairW K X Y:= by
    funext n; simp only [bond,promised,paired,Pi.add_apply,h,map_sum, Finset.sum_add_distrib ]
lemma fixT (L:Pair (Glade G I))(h:∀ i j k, L (F i) (joint G I (X j) (Y k))=joint G I ( L (F i) (X j)) (Y k)+joint G I ( X j ) (L (F i) (Y k))): pairW L F (bond G I X Y)= bond G I (pairW L F X) Y+ bond G I X (pairW L F Y):= by
    let P:= SplitP.nat; let E:= Glade G I; funext i; simp_rw [bond, Pi.add_apply, paired, map_sum,h,Finset.sum_add_distrib, LinearMap.sum_apply ]; refine congr_arg₂ (·+·) (P.trip E _ (fun x y z=> joint G I ( L (F x) (X y) ) ( Y z ))) ( Puff.Engine.rewrap P E (fun x y z=>joint G I ( X y ) (L ( F x ) (Y z) )) i )
abbrev Share (G:Gauge)(I:Type):= pairW (voyage (fun _ : I=> lineA G) false)
abbrev Touch (G:Gauge)(I:Type):= pairW (voyage (fun _ : I=> lineB G) true)
lemma helm_charge (h:X∈(glaze G I).guard) : helm M η (bond G I X Y)= bond G I (helm M η X) Y+ bond G I X (helm M η Y)+ Share G I X Y:= by
    let U:= gather M η; let H:=glazeV.mp h;
    have L(x y z:ℕ) (i:I)(s:ℝ): Pure (field Landau.parity) false (U x i s) := (glazeV.mp ( hedge ( plenary M ) ) x i s).2
    unfold helm; simp_rw [ LinearMap.add_apply,map_add,LinearMap.add_apply ]; rw [fixm (A).P ( voyage (fun _ : I=> lineA G) false ) (X:=X) (Y:=Y) (fun i j=> funext fun k=> funext (fun s=> pira (H i k s))),fixT (A).X (F:= gather M η) (X:=X) (Y:=Y) (fun i j k=> funext fun p=> funext fun v=> tree_derive (cl_a G v 0) (L i j k p v) ( H j p v|>.2 )) ]; unfold Share; abel
lemma nav_charge (h:X∈(glaze G I).guard): nav M η (bond G I X Y)= bond G I (nav M η X) Y+ bond G I X ( nav M η Y)+ Touch G I X Y:= by
    let U:= gather M η; let H:=glazeV.mp h; obtain hv:= hedge ( plenary (η:=η) M )
    unfold nav; simp_rw [ LinearMap.add_apply,map_add,LinearMap.add_apply ]; rw [fixm (A).J ( voyage (fun _ : I=> lineB G) true ) ( X:=X ) (Y:=Y) ( fun i j=> funext fun k=> funext (fun s=> gira (H i k s))),fixT (A).C (F:=gather M η) (X:=X) (Y:=Y) (fun i j k=> funext fun p=> funext fun v=> tree_derive (cl_b G v 0) (( glazeV.mp hv i p v ).2) ((H j p v).2)) ]; unfold Touch; abel
lemma share_graft (h:F∈(glaze G I).guard)(ht:X∈ (glaze G I).guard)(he:Banks Y q) : Share G I F (bond G I X Y) = bond G I (Share G I F X) Y+ bond G I X (Share G I F Y) := fixT _ (fun i j k=>funext fun p=> funext fun v=> cr_derive rA ( cl_a G v 0 ) (( glazeV.mp h ) i p v) (( glazeV.mp ht ) j p v) ( he k|>.invoice ))
lemma touch_graft (h:F∈(glaze G I).guard)(ht:X∈(glaze G I).guard)(he:Banks Y q): Touch G I F (bond G I X Y)= bond G I (Touch G I F X) Y+ bond G I X (Touch G I F Y):= fixT _ (fun i j k=> funext fun p=> funext fun v=> cr_derive rB (cl_b G v 0) (glazeV.mp h i p v) (glazeV.mp ht j p v) (he k|>.invoice))
lemma tiered (h:X∈(glaze G I).guard): pairW (both G I).X ( gather M η ) X ∈ (glaze G I).guard:= by
    let V:=gather M η; have hp:= hedge ( plenary (η:=η) M ); refine glazeV.mpr (fun k p v=> ?_ ); simp only [ paired, Finset.sum_apply ]; refine (Roof G).sum_mem (fun i _=> ?_); obtain ⟨h1,h2⟩:= (glazeV.mp hp i.1 p v); obtain ⟨h3,h4⟩:= glazeV.mp h i.2 p v; exact ⟨ rA.on_tree h1 h3,tree_pure (cl_a G v 0) h2 h4⟩
def plants (G:Gauge)(I:Type) : Puff.Engine (glaze G I):= ( Station I (fun _=> Station ℝ (fun s=> Move G s)) ).liftV SplitP.nat
lemma plants_H (G:Gauge)(I:Type): (plants G I).move= promote (both G I).P:= rfl
lemma foliage (G:Gauge)(I:Type): (plants G I).join= Share G I := rfl
lemma clearT (F:Law G)(V:Latch.Edge G) : tree Landau.parity V F (Koszul.coin (1:ℂ))=0:= by funext l; rw [tree,scatter_congr _ l _ (fun _ _=>(0:ℂ)) ?_]; exact map_zero (allocate ..); intro a b hb; simp [attaches,coin]
lemma plants_unit : pairW (A).X (gather M η) (glaze G I).unit= 0:= by
    funext n; rw [paired]; apply Finset.sum_eq_zero; intro i _; by_cases hv:i.2=0
    · have he: (glaze G I).unit 0= (hori G I).unit:= by simp [ Actors.stack,SplitP.refineV,glaze,SplitP.nat ]
      rw [hv,he]; exact funext fun k=> funext fun t=> clearT _ _
    rw [ show (glaze G I).unit i.2=0 from ( by simp [glaze, Actors.stack,SplitP.refineV,SplitP.nat,hv] ), map_zero ]
def team (M:MS_Data G K)(η:I→ℝ): Puff.Engine ( glaze G I ) :={ plants G I with
    move:= helm M η
    stays:= fun i he=> (glaze G I).guard.add_mem ( (plants G I).stays i he) (tiered he)
    unitLaw:= by rw [helm,LinearMap.add_apply,plants_unit,add_zero, ← plants_H ]; exact (plants G I).unitLaw
    compatibility:= fun _ _ h _=> helm_charge h }
end YM.FVA2.O.Serve
