/**

    Setup for writing rules for Aave Token v3 

*/

/**
    Public methods from the AaveTokenV3Harness.sol
*/

methods{
    totalSupply() returns (uint256) envfree
    balanceOf(address addr) returns (uint256) envfree
    transfer(address to, uint256 amount) returns (bool)
    transferFrom(address from, address to, uint256 amount) returns (bool)
    delegate(address delegatee)
    metaDelegate(address, address, uint256, uint8, bytes32, bytes32)
    getPowerCurrent(address user, uint8 delegationType) returns (uint256) envfree
    getBalance(address user) returns (uint104) envfree
    getDelegatedPropositionBalance(address user) returns (uint72) envfree
    getDelegatedVotingBalance(address user) returns (uint72) envfree
    getDelegatingProposition(address user) returns (bool) envfree
    getDelegatingVoting(address user) returns (bool) envfree
    getVotingDelegate(address user) returns (address) envfree
    getPropositionDelegate(address user) returns (address) envfree
}

/**

    Constants

*/
// GovernancyType enum from the token contract
definition VOTING_POWER() returns uint8 = 0;
definition PROPOSITION_POWER() returns uint8 = 1;

definition DELEGATED_POWER_DIVIDER() returns uint256 = 10^10;

// 16000000 * 10^18 is the maximum supply of the AAVE token
definition MAX_DELEGATED_BALANCE() returns uint256 = 16000000 * 10^18 / DELEGATED_POWER_DIVIDER();

/**

    Function that normalizes (removes 10 least significant digits) a given param. 
    It mirrors the way delegated balances are stored in the token contract. Since the delegated
    balance is stored as a uint72 variable, delegated amounts (uint256()) are normalized.

*/

function normalize(uint256 amount) returns uint256 {
    return to_uint256(amount / DELEGATED_POWER_DIVIDER() * DELEGATED_POWER_DIVIDER());
}

/**

    Testing correctness of delegate(). An example of a unit test

*/

rule delegateCorrectness(address bob) {
    env e;
    // delegate not to self or to zero
    require bob != e.msg.sender && bob != 0;

    uint256 bobDelegatedBalance = getDelegatedVotingBalance(bob);
    // avoid unrealistic delegated balance
    require(bobDelegatedBalance < MAX_DELEGATED_BALANCE());
    
    // verify that the sender doesn't already delegate to bob
    address delegateBefore = getVotingDelegate(e.msg.sender);
    require delegateBefore != bob;

    uint256 bobVotingPowerBefore = getPowerCurrent(bob, VOTING_POWER());
    uint256 delegatorBalance = balanceOf(e.msg.sender);

    delegate(e, bob);

    // test the delegate indeed has changed to bob
    address delegateAfter = getVotingDelegate(e.msg.sender);
    assert delegateAfter == bob;

    // test the delegate's new voting power
    uint256 bobVotingPowerAfter = getPowerCurrent(bob, VOTING_POWER());
    assert bobVotingPowerAfter == bobVotingPowerBefore + normalize(delegatorBalance);
}

/**

    Verify that only delegate functions can change someone's delegate.
    An example for a parametric rule.

*/

rule votingDelegateChanges(address alice, method f) {
    env e;
    calldataarg args;

    address aliceDelegateBefore = getVotingDelegate(alice);

    f(e, args);

    address aliceDelegateAfter = getVotingDelegate(alice);

    // only these four function may change the delegate of an address
    assert aliceDelegateAfter != aliceDelegateBefore =>
        f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector;
}

/**

    A ghost variable that tracks the sum of all addresses' balances

*/
ghost mathint sumBalances {
    init_state axiom sumBalances == 0;
}

/**

    This hook updates the sumBalances ghost whenever any address balance is updated

*/
hook Sstore _balances[KEY address user].balance uint104 balance
    (uint104 old_balance) STORAGE {
        sumBalances = sumBalances - to_mathint(old_balance) + to_mathint(balance);
    }

/**

    Invariant: 
    sum of all addresses' balances should be always equal to the total supply of the token
    
*/
invariant totalSupplyEqualsBalances()
    sumBalances == totalSupply()

//NEW RULES

/**
    1-
    Invariant: 
    Verify that zero address cannot have balance.

*/

invariant zeroAddressHasNoBalance()
    balanceOf(0) == 0

/**
    2-
    Invariant:
    Verify that zero address has no power.

*/
invariant zeroAddrNoPower()
    getPowerCurrent(0, VOTING_POWER()) == 0 && getPowerCurrent(0, PROPOSITION_POWER()) == 0
    {preserved {
        requireInvariant zeroAddressHasNoBalance();
    }}

/**
    3-
    Invariant:
    Verify that the (voting power) of an address that isn't delegating his power and isn't calling any delegate function, equals (balance + delegatedVotingBalance).

*/
invariant accountVotingPower(address someone)
    balanceOf(someone) + getDelegatedVotingBalance(someone)*DELEGATED_POWER_DIVIDER() == getPowerCurrent(someone, VOTING_POWER())
    //coverage of all fuctions except delegate ones
    filtered {
        f -> f.selector != delegate(address).selector && 
        f.selector != delegateByType(address,uint8).selector && 
        f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector && 
        f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector
    }
    
    {preserved {
        //require user "someone" is not delegating before
        require(!getDelegatingVoting(someone));
    }}

/**
    4-
    Invariant:
    Verify that the (proposition power) of an address that isn't delegating his power and isn't calling any delegate function, equals (balance + delegatedPropositionBalance).

*/
invariant accountPropositionPower(address someone)
    balanceOf(someone) + getDelegatedPropositionBalance(someone)*DELEGATED_POWER_DIVIDER() == getPowerCurrent(someone, PROPOSITION_POWER())
    //coverage of all fuctions except delegate ones
    filtered {
        f -> f.selector != delegate(address).selector && 
        f.selector != delegateByType(address,uint8).selector && 
        f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector && 
        f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector
    }
    
    {preserved {
        //require user "someone" is not delegating before
        require(!getDelegatingProposition(someone));
    }}

/**
    5-
    Invariant:
    Verify that the (voting power) of an address that is delegating his power and isn't calling any delegate function, equals (delegatedVotingBalance)

*/
invariant delegatingAccountVotingPower(address someone)
    getDelegatedVotingBalance(someone)*DELEGATED_POWER_DIVIDER() == getPowerCurrent(someone, VOTING_POWER())
    //coverage of all fuctions except delegate ones
    filtered {
        f -> f.selector != delegate(address).selector && 
        f.selector != delegateByType(address,uint8).selector && 
        f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector && 
        f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector
    }
    
    {preserved {
        //require user "someone" is delegating before
        require(getDelegatingVoting(someone));
    }}

/**
    6-
    Invariant:
    Verify that the (proposition power) of an address that is delegating his power and isn't calling any delegate function, equals (delegatedPropositionBalance).

*/
invariant delegatingAccountPropositionPower(address someone)
    getDelegatedPropositionBalance(someone)*DELEGATED_POWER_DIVIDER() == getPowerCurrent(someone, PROPOSITION_POWER())
    //coverage of all fuctions except delegate ones
    filtered {
        f -> f.selector != delegate(address).selector && 
        f.selector != delegateByType(address,uint8).selector && 
        f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector && 
        f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector
    }
    
    {preserved {
        //require user "someone" is delegating before
        require(getDelegatingProposition(someone));
    }}


/**
    7-
    Invariant:
    Verify that the (voting power) of an address that is delegating his power and calls a delegate function, equals (balance + delegatedVotingBalance)

*/
invariant delegatingAccountVotingPowerCallingDelegate(address someone)
    balanceOf(someone) + getDelegatedVotingBalance(someone)*DELEGATED_POWER_DIVIDER() == getPowerCurrent(someone, VOTING_POWER())
    //coverage of delegate fuctions
    filtered {
        f -> f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector
    }
    {preserved {
        //require user "someone" is delegating before
        require(getDelegatingVoting(someone));
    }}

/**
    8-
    Invariant:
    Verify that the (Proposition power) of an address that is delegating his power and calls a delegate function, equals (balance + delegatedPropositionBalance)

*/
invariant delegatingAccountPropositionPowerCallingDelegate(address someone)
    balanceOf(someone) + getDelegatedPropositionBalance(someone)*DELEGATED_POWER_DIVIDER() == getPowerCurrent(someone, PROPOSITION_POWER())
    //coverage of delegate fuctions
    filtered {
        f -> f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector
    }
    {preserved {
        //require user "someone" is delegating before
        require(getDelegatingProposition(someone));
    }}

/**
    9-
    Invariant:
    Verify that the (voting power) of an address that is not delegating his power and calls a delegate function, equals (delegatedVotingBalance)

*/
invariant noDelegatingAccountVotingPowerCallingDelegate(address someone)
    getDelegatedVotingBalance(someone)*DELEGATED_POWER_DIVIDER() == getPowerCurrent(someone, VOTING_POWER())
    //coverage of delegate fuctions
    filtered {
        f -> f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector
    }
    {preserved {
        //require user "someone" is not delegating before
        require(!getDelegatingVoting(someone));
    }}

/**
    10-
    Invariant
    Verify that the (Proposition power) of an address that is not delegating his power and calls a delegate function, equals (delegatedPropositionBalance)

*/
invariant noDelegatingAccountPropositionPowerCallingDelegate(address someone)
    getDelegatedPropositionBalance(someone)*DELEGATED_POWER_DIVIDER() == getPowerCurrent(someone, PROPOSITION_POWER())
    //coverage of delegate fuctions
    filtered {
        f -> f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector
    }
    {preserved {
        //require user "someone" is not delegating before
        require(!getDelegatingProposition(someone));
    }}

/**
    11-
    Verify that only ERC20 functions can change someone's balance.

*/
rule balanceChanges(address alice, method f) {
    env e;
    calldataarg args;

    uint aliceBalanceBefore = balanceOf(alice);

    f(e, args);

    uint aliceBalanceAfter = balanceOf(alice);

    // only these four function may change the delegate of an address
    assert aliceBalanceBefore != aliceBalanceAfter =>
        f.selector == transfer(address,uint256).selector || 
        f.selector == transferFrom(address,address,uint256).selector;
}

/**
    12-
    The delegator can always revoke his voting power only by calling delegating functions 

*/
rule checkRevokingVotingPower(address someone, method f) {
    env e;
    calldataarg args;

    //store voting delegating state before
    bool delegatingStateBefore = getDelegatingVoting(someone);
    //transacction
    f(e, args);
    //store voting delegating state after
    bool delegatingStateAfter = getDelegatingVoting(someone);

    assert (delegatingStateBefore => (delegatingStateAfter || !delegatingStateAfter));
    //assert that any delagation granted can be rovoked or changed to another delegatee using delegate functions
    assert ((delegatingStateBefore &&  !delegatingStateAfter )=>
        f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector);
}

/**
    13-
    The delegator can always revoke his proposition power only by calling delegating functions 

*/
rule checkRevokingPropositionPower(address someone, method f) {
    env e;
    calldataarg args;

    //store proposition delegating state before
    bool delegatingStateBefore = getDelegatingProposition(someone);
    //transacction
    f(e, args);
    //store proposition delegating state after
    bool delegatingStateAfter = getDelegatingProposition(someone);

    assert (delegatingStateBefore => (delegatingStateAfter || !delegatingStateAfter));
    //assert that any delagation granted can be rovoked or changed to another delegatee using delegate functions
    assert ((delegatingStateBefore &&  !delegatingStateAfter )=>
        f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector ||
        f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector);
}

/**
    14-
    Any change to one type of delegation does not affect the other type 

*/
rule checkIndividualDelegationChange(address bob){
    env e;
    // delegate not to self or to zero
    require bob != e.msg.sender && bob != 0;
    uint8 delegateType;

    //powers before transaction
    uint256 votingPowerBefore = getDelegatedVotingBalance(bob);
    uint256 proposalPowerBefore = getDelegatedPropositionBalance(bob);
    // avoid unrealistic delegated balance
    require(votingPowerBefore < MAX_DELEGATED_BALANCE());
    require(proposalPowerBefore < MAX_DELEGATED_BALANCE());
    
    // verify that the sender doesn't already delegate to bob
    address delegatePropositionBefore = getPropositionDelegate(e.msg.sender);
    address delegateVotingBefore = getVotingDelegate(e.msg.sender);
    require delegatePropositionBefore != bob;
    require delegateVotingBefore != bob;

    delegateByType(e, bob, delegateType);

    uint256 votingPowerAfter = getDelegatedVotingBalance(bob);
    uint256 proposalPowerAfter = getDelegatedPropositionBalance(bob);


    //verify that if the type selected is voting, proposition power has not change and viceversa
    assert delegateType == VOTING_POWER() => proposalPowerBefore == proposalPowerAfter;
    assert delegateType != VOTING_POWER() => votingPowerBefore == votingPowerAfter;
}

/*
    15-
    The voting delegatee of some account changes only if they are the one requesting it 

**/
rule delegateeVotingChange(method f){
    address account;
    env e;
    calldataarg args;     
    
    //check that both addresses are different
    require account != e.msg.sender;
    
    //store delegatee of account before the transaction and require it is delegating
    address delegateeBefore = getVotingDelegate(account);
    require getDelegatingVoting(account);

    //call delegate transactions from e.msg.sender
    f(e, args);
    //only for Normal Delegate transanctions
    require (f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector);

    //store delegatee of account after the transaction
    address delegateeAfter = getVotingDelegate(account);
      
    //check account delegatee has not change
    assert delegateeBefore == delegateeAfter;
}

/*
    16-
    The Proposition delegatee of some account changes only if they are the one requesting

**/
rule delegateePropositionChange(method f){
    address account;
    env e;
    calldataarg args;     
    
    //check that both addresses are different
    require account != e.msg.sender;
    
    //store delegatee of account before the transaction and require it is delegating
    address delegateeBefore = getPropositionDelegate(account);
    require getDelegatingProposition(account);

    //call delegate transactions from e.msg.sender
    f(e, args);
    //only for Normal Delegate transanctions
    require (f.selector == delegate(address).selector || 
        f.selector == delegateByType(address,uint8).selector);

    //store delegatee of account after the transaction
    address delegateeAfter = getPropositionDelegate(account);
      
    //check account delegatee has not change
    assert delegateeBefore == delegateeAfter;
}


/*
    17-
    With MetaDelegate functions if a user changes another account's voting delegatee, his delegatee wont change

**/
rule delegateeVotingMetaChange(method f){
    address account;
    env e;
    calldataarg args;     
    
    //check that both addresses are different
    require account != e.msg.sender;

    //store delegatees of account and msg.sender before transaction
    address delegateeBefore = getVotingDelegate(account);
    address delegateeBeforeSender = getVotingDelegate(e.msg.sender);

    //require account is delegating
    require getDelegatingVoting(account);

    //Call Meta-delegate transactions from e.msg.sender
    f(e, args);
    require (f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector);

    //store delegatees of account and msg.sender after transaction
    address delegateeAfter = getVotingDelegate(account);
    address delegateeAfterSender = getVotingDelegate(e.msg.sender);

    //if account delegate has changed msg.sender delegate should not change
    assert delegateeBefore != delegateeAfter => delegateeBeforeSender == delegateeAfterSender;
}

/*
    18-
    With MetaDelegate functions if a user changes another account's delegatee, his delegatee wont change

**/
rule delegateePropositionMetaChange(method f){
    address account;
    env e;
    calldataarg args;     
    
    //check that both addresses are different
    require account != e.msg.sender;

    //store delegatees of account and msg.sender before transaction
    address delegateeBefore = getPropositionDelegate(account);
    address delegateeBeforeSender = getPropositionDelegate(e.msg.sender);
    
    //require account is delegating
    require getDelegatingProposition(account);

    //Meta-delegate transactions
    f(e, args);
    require (f.selector == metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector ||
        f.selector == metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector);

    //store delegatees of account and msg.sender after transaction
    address delegateeAfter = getPropositionDelegate(account);
    address delegateeAfterSender = getPropositionDelegate(e.msg.sender);

    //if account delegate has changed msg.sender delegate should not change
    assert delegateeBefore != delegateeAfter => delegateeBeforeSender == delegateeAfterSender;
}

/* 
    19-
    Voting Power of a delegatee is always Equal or bigger than the balanace of the delegator

*/

invariant VotingPowerEqualBiggerDelegator(address someone)
    getDelegatedVotingBalance(getVotingDelegate(someone))*DELEGATED_POWER_DIVIDER() >= balanceOf(someone) 
    
    //Filter out delegating and transfer functions that do internal changes on balances and delegating balances
    filtered {
        f -> f.selector != delegate(address).selector && 
        f.selector != delegateByType(address,uint8).selector && 
        f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector && 
        f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector &&
        f.selector != transfer(address,uint256).selector &&
        f.selector != transferFrom(address,address,uint256).selector &&
        f.selector != _governancePowerTransferByType(uint104,uint104,address,uint8).selector
    }
    //Require that delegator is delegating
    {preserved {
        require(getDelegatingVoting(someone));
    }}

/* 
    20-
    Proposition Power of a delegatee is always Equal or bigger than the balanace of the delegator

*/

invariant PropositionPowerEqualBiggerDelegator(address someone)
    getDelegatedPropositionBalance(getPropositionDelegate(someone))*DELEGATED_POWER_DIVIDER() >= balanceOf(someone) 
    
    //Filter out delegating and transfer functions that do internal changes on balances and delegating balances
    filtered {
        f -> f.selector != delegate(address).selector && 
        f.selector != delegateByType(address,uint8).selector && 
        f.selector != metaDelegate(address,address,uint256,uint8,bytes32,bytes32).selector && 
        f.selector != metaDelegateByType(address,address,uint8,uint256,uint8,bytes32,bytes32).selector &&
        f.selector != transfer(address,uint256).selector &&
        f.selector != transferFrom(address,address,uint256).selector &&
        f.selector != _governancePowerTransferByType(uint104,uint104,address,uint8).selector
    }
    //Require that delegator is delegating
    {preserved {
        require(getDelegatingProposition(someone));
    }}








