document.getElementById('generateTreeButton').addEventListener('click', function() {
    checkUserAnswer()
})

function checkUserAnswer() {
    var imps = get_literals()
    if (imps) {
        if (checkAnswer(imps)) {
            changeFeedback('Correct! Move onto next exercise.')
            var inputs = document.querySelectorAll('.litInput')
            for (var i = 0; i < inputs.length; i++) {
                inputs[i].disabled = true
            }
            setCookie('exercise1', '1', 7)
        } else {
            appendFeedback(" Literals are case sensitive and the '->' must not contain a space between the characters.")
        }
    } 
  
}

function checkAnswer(imps) {
    var answers = [['A', 'B'], ['B', 'C']]
    for (var i = 0; i < answers.length; i++) {
        var found = false
        for (var n = 0; n < imps.length; n++) {
            if (answers[i][0] == imps[n][0] && answers[i][1] == imps[n][1]) {
                found = true
            }
        }
        if (!found) {
            changeFeedback(`Couldn't find implication for the literals: [${answers[i]}].`)
            return false
        }
    }
    return true
}

function get_literals() {
    var inputs = document.querySelectorAll('.litInput')
    var imp_list = []
    for (var i = 0; i < inputs.length; i++) {
        if (!inputs[i].value == '') {
            var temp_list = inputs[i].value.trim().split("->")
            var corrected = []
            if (temp_list.length > 2) {
                changeFeedback("Please don't place more than 1 implication per text box")
                return false
            } else {
                temp_list_2 = temp_list[0].split(' ').concat(temp_list[1].split(' '))
            }
            temp_list = []
            for (var n = 0; n < temp_list_2.length; n++) {
                if (!temp_list_2[n] == "") {
                    temp_list.push(temp_list_2[n])
                }
            }
            if (temp_list.length > 2) {
                changeFeedback('Please only have two literals per input')
                return false
            }
            for (var n = 0; n < temp_list.length; n++) {
                if (!(temp_list[n] === '')) {
                    corrected.push(temp_list[n])
                }
            }
            if (corrected.includes('T')){
                changeFeedback('Please do not use the literal T as this stands for True')
                return false
            } else if (corrected.includes('F')) {
                changeFeedback('Please do not use the literal F as this stands for False')
                return false
            } else {
                imp_list.push([corrected[0], corrected[corrected.length - 1]])
            }
        } else {
            changeFeedback('Please remove empty text boxes')
            return false
        }
        
        
    }
    return imp_list
}

function changeFeedback(str) {
    document.getElementById('userFeed').textContent = str
}

function appendFeedback(str) {
    document.getElementById('userFeed').textContent = document.getElementById('userFeed').textContent + str
}

function setCookie(name,value,days) {
    var expires = "";
    if (days) {
        var date = new Date();
        date.setTime(date.getTime() + (days*24*60*60*1000));
        expires = "; expires=" + date.toUTCString();
    }
    document.cookie = name + "=" + (value || "")  + expires + "; path=/";
}