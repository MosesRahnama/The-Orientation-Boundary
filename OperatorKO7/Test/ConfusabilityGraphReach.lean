import OperatorKO7.Meta.OperationalInexpressibility.ConfusabilityGraph

set_option autoImplicit false

open OperatorKO7.Meta.OperationalInexpressibility.Confusability

#check @Confusable
#check @confusabilityGraph
#check @confusabilityGraph_adj_iff
#check @ResolvingSideChannel
#check @augmentObserver
#check @licensed_augment_iff_resolving
#check @licensed_augment_equiv
#check @exists_resolving_channel_congr
#check @coloringOfResolving
#check @coloringOfResolving_apply
#check @resolving_of_coloring
#check @licensed_augment_of_coloring
#check @colorable_iff_exists_fin_resolving_channel
#check @chromaticNumber_le_iff_exists_fin_resolving_channel
#check @sameFiber_target_ne_forces_side_ne
#check @constantObserver_adj_iff_target_ne
#check @binaryFixtureObserver
#check @binaryFixtureTarget
#check binaryFixture_has_edge
#check binaryFixture_has_nonedge
#check @binaryFixtureSide
#check @binaryFixtureSide_eq_iff_target_eq
#check binaryFixtureSide_licenses

#print axioms Confusable
#print axioms confusabilityGraph
#print axioms confusabilityGraph_adj_iff
#print axioms ResolvingSideChannel
#print axioms augmentObserver
#print axioms licensed_augment_iff_resolving
#print axioms licensed_augment_equiv
#print axioms exists_resolving_channel_congr
#print axioms coloringOfResolving
#print axioms coloringOfResolving_apply
#print axioms resolving_of_coloring
#print axioms licensed_augment_of_coloring
#print axioms colorable_iff_exists_fin_resolving_channel
#print axioms chromaticNumber_le_iff_exists_fin_resolving_channel
#print axioms sameFiber_target_ne_forces_side_ne
#print axioms constantObserver_adj_iff_target_ne
#print axioms binaryFixtureObserver
#print axioms binaryFixtureTarget
#print axioms binaryFixture_has_edge
#print axioms binaryFixture_has_nonedge
#print axioms binaryFixtureSide
#print axioms binaryFixtureSide_eq_iff_target_eq
#print axioms binaryFixtureSide_licenses

#check @colorable_iff_fiberMultiplicity_le
#print axioms colorable_iff_fiberMultiplicity_le
#check @chromaticNumber_eq_fiberMultiplicity
#print axioms chromaticNumber_eq_fiberMultiplicity
#check @fiberCodeDeficit_eq_clog_chromaticNumber
#print axioms fiberCodeDeficit_eq_clog_chromaticNumber
#check @exists_binary_resolving_channel_iff
#print axioms exists_binary_resolving_channel_iff
#check @fiberCodeDeficit_isLeast_binary_resolving_length
#print axioms fiberCodeDeficit_isLeast_binary_resolving_length
#check @binaryFixture_chromaticNumber
#print axioms binaryFixture_chromaticNumber
#check @binaryFixture_binary_capacity
#print axioms binaryFixture_binary_capacity

#check @FiberTargetValues
#print axioms FiberTargetValues
#check @fiberTargetRepresentative
#print axioms fiberTargetRepresentative
#check @fiberTargetRepresentative_spec
#print axioms fiberTargetRepresentative_spec
#check @fiberTargetEmbeddingOfLicense
#print axioms fiberTargetEmbeddingOfLicense
#check @sideChannelOfFiberEmbeddings
#print axioms sideChannelOfFiberEmbeddings
#check @sideChannelOfFiberEmbeddings_licensed
#print axioms sideChannelOfFiberEmbeddings_licensed
#check @exists_resolving_channel_iff_fiber_embeddings
#print axioms exists_resolving_channel_iff_fiber_embeddings
#check @exists_fin_resolving_channel_iff_fiber_capacity
#print axioms exists_fin_resolving_channel_iff_fiber_capacity
#check @exists_finite_resolving_channel_iff_fiber_capacity
#print axioms exists_finite_resolving_channel_iff_fiber_capacity
#check @colorable_iff_fiber_capacity
#print axioms colorable_iff_fiber_capacity
#check @chromaticNumber_le_iff_fiber_capacity
#print axioms chromaticNumber_le_iff_fiber_capacity
#check @exists_binary_resolving_channel_iff_fiber_capacity
#print axioms exists_binary_resolving_channel_iff_fiber_capacity
#check @one_symbol_channel_iff_licensed
#print axioms one_symbol_channel_iff_licensed
#check @zero_symbol_channel_iff_isEmpty
#print axioms zero_symbol_channel_iff_isEmpty
#check @no_fin_channel_of_infinite_fiber
#print axioms no_fin_channel_of_infinite_fiber
#check @no_fin_channel_of_unbounded_fibers
#print axioms no_fin_channel_of_unbounded_fibers
#check @natParitySide
#print axioms natParitySide
#check @natParitySide_licenses
#print axioms natParitySide_licenses
#check @natParity_no_one_symbol
#print axioms natParity_no_one_symbol
#check @nat_identity_no_finite_channel
#print axioms nat_identity_no_finite_channel

open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

example : natParitySide 3 = (1 : Fin 2) := rfl

example : ∃ s : Nat → Fin 2,
    Licensed (augmentObserver (fun _ : Nat => ()) s) (fun x : Nat => x % 2) :=
  ⟨natParitySide, natParitySide_licenses⟩

example : ∀ o : Unit,
    Finite (FiberTargetValues (fun _ : Nat => ()) (fun x : Nat => x % 2) o) ∧
      Nat.card (FiberTargetValues (fun _ : Nat => ()) (fun x : Nat => x % 2) o) ≤ 2 :=
  (exists_fin_resolving_channel_iff_fiber_capacity _ _ 2).mp
    ⟨natParitySide, natParitySide_licenses⟩

example :
    (confusabilityGraph (fun _ : Nat => ()) (fun x : Nat => x % 2)).chromaticNumber ≤ 2 :=
  (chromaticNumber_le_iff_exists_fin_resolving_channel _ _ 2).mpr
    ⟨natParitySide, natParitySide_licenses⟩

example (n : Nat) : ¬ ∃ s : Nat → Fin n,
    Licensed (augmentObserver (fun _ : Nat => ()) s) id :=
  nat_identity_no_finite_channel n

example {X Q V : Type} [IsEmpty X] (q : X → Q) (P : X → V) :
    ∃ s : X → Fin 0, Licensed (augmentObserver q s) P :=
  (zero_symbol_channel_iff_isEmpty q P).mpr inferInstance

#check @chromaticNumber_eq_top_iff_fiber_obstructions
#print axioms chromaticNumber_eq_top_iff_fiber_obstructions
#check @growingFiberObserver
#print axioms growingFiberObserver
#check @growingFiberTarget
#print axioms growingFiberTarget
#check @growingFiberEquiv
#print axioms growingFiberEquiv
#check @growingFiber_finite
#print axioms growingFiber_finite
#check @growingFiber_card
#print axioms growingFiber_card
#check @growingFiber_no_finite_channel
#print axioms growingFiber_no_finite_channel
#check @nat_identity_fiber_infinite
#print axioms nat_identity_fiber_infinite
#check @nat_card_without_finite_is_insufficient
#print axioms nat_card_without_finite_is_insufficient
#check @orbit_refines_stabilized_observer
#print axioms orbit_refines_stabilized_observer
#check @fixed_channel_licenses_all_iff_at_image_bound
#print axioms fixed_channel_licenses_all_iff_at_image_bound
#check @exists_fixed_channel_all_iff_at_image_bound
#print axioms exists_fixed_channel_all_iff_at_image_bound
#check @exists_fixed_channel_iff_stagewise_channels
#print axioms exists_fixed_channel_iff_stagewise_channels
#check @permanent_fin_channel_iff_fiber_capacity
#print axioms permanent_fin_channel_iff_fiber_capacity
#check @permanent_finite_alphabet_channel_iff_fiber_capacity
#print axioms permanent_finite_alphabet_channel_iff_fiber_capacity
#check @finite_channel_set_isClosed
#print axioms finite_channel_set_isClosed
#check @finite_channel_compactness
#print axioms finite_channel_compactness
#check @finite_alphabet_compactness
#print axioms finite_alphabet_compactness
#check @coarsening_fixed_finite_channel_iff_stagewise
#print axioms coarsening_fixed_finite_channel_iff_stagewise
#check @coarsening_fixed_finite_alphabet_iff_stagewise
#print axioms coarsening_fixed_finite_alphabet_iff_stagewise
#check @threePairObserver
#print axioms threePairObserver
#check @threePair_stagewise_two_symbols
#print axioms threePair_stagewise_two_symbols
#check @threePair_no_common_two_symbols
#print axioms threePair_no_common_two_symbols
#check @threePair_not_coarsening
#print axioms threePair_not_coarsening


example : Nat.card (FiberTargetValues growingFiberObserver growingFiberTarget 0) = 1 := by
  simpa only [Nat.zero_add] using growingFiber_card 0

example :
    (∀ n, Finite (FiberTargetValues growingFiberObserver growingFiberTarget n)) ∧
      ∀ m, ¬ ∃ s : (Σ k : Nat, Fin (k + 1)) → Fin m,
        Licensed (augmentObserver growingFiberObserver s) growingFiberTarget :=
  ⟨growingFiber_finite, growingFiber_no_finite_channel⟩

example :
    (∀ o : Unit, Nat.card (FiberTargetValues (fun _ : Nat => ()) (id : Nat → Nat) o) ≤ 0) ∧
      ¬ ∃ s : Nat → Fin 0, Licensed (augmentObserver (fun _ : Nat => ()) s) id :=
  nat_card_without_finite_is_insufficient 0

example :
    (confusabilityGraph (fun _ : Nat => ()) (id : Nat → Nat)).chromaticNumber = ⊤ := by
  apply (chromaticNumber_eq_top_iff_fiber_obstructions _ _).mpr
  intro n
  refine ⟨(), Or.inl ?_⟩
  intro hf
  letI := nat_identity_fiber_infinite
  exact hf.false

example :
    (∀ n : Nat, ∃ x y : Nat, x - n ≠ y - n ∧ x - (n + 1) = y - (n + 1)) ∧
      ∃ s : Nat → Fin 2, ∀ n,
        Licensed (augmentObserver (fun x : Nat => x - n) s) (fun x : Nat => x % 2) := by
  refine ⟨?_, ?_⟩
  · intro n
    exact ⟨0, n + 1, by omega, by omega⟩
  · have hc : ∀ n, ObserverRefines
        (fun x : Nat => x - n) (fun x : Nat => x - (n + 1)) := by
      intro n x y h
      change x - n = y - n at h
      change x - (n + 1) = y - (n + 1)
      omega
    apply (coarsening_fixed_finite_channel_iff_stagewise
      (fun n x : Nat => x - n) hc (fun x : Nat => x % 2) 2).mpr
    intro n
    exact ⟨natParitySide, fun _ _ h => congrArg Fin.val (congrArg Prod.snd h)⟩

example :
    (∀ i : Fin 3, ∃ s : Fin 3 → Fin 2,
      Licensed (augmentObserver (threePairObserver i) s) id) ∧
      ¬ ∃ s : Fin 3 → Fin 2, ∀ i : Fin 3,
        Licensed (augmentObserver (threePairObserver i) s) id :=
  ⟨threePair_stagewise_two_symbols, threePair_no_common_two_symbols⟩

example :
    ∃ s : Bool → Fin 2, ∀ n,
      Licensed (augmentObserver
        (OperatorKO7.Meta.OperationalInexpressibility.FiniteObserverRecurrence.orbitObserver
          (fun _ : Bool => false) id n) s) id := by
  refine ⟨fun b => if b then 1 else 0, ?_⟩
  intro n x y h
  have hs := congrArg Prod.snd h
  cases x <;> cases y <;> simp_all [augmentObserver]
