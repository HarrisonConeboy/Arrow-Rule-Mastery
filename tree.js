function not_literal(literal) {
    var output
    if (literal.startsWith('!')) {
        return literal.slice(1,2)
    } else {
        return '!' + literal
    } 
}

function contra_positive(implication) {
    return [not_literal(implication[1]), not_literal(implication[0])]
}


// Truth table generation
function countLiterals(imp_set) {
    var uniqueLiterals = []
    for (let i = 0; i < imp_set.length; i++) {
        var imp = imp_set[i]
        if (imp[0].startsWith('!')) {
            var pred = not_literal(imp[0])
        } else {
            var pred = imp[0]
        }
        if (imp[1].startsWith('!')) {
            var cons = not_literal(imp[1])
        } else {
            var cons = imp[1]
        }
        if (!uniqueLiterals.includes(pred)) {
            uniqueLiterals.push(pred)
        }
        if (!uniqueLiterals.includes(cons)) {
            uniqueLiterals.push(cons)
        }
    }
    return uniqueLiterals
}
  
function produce_truth_table(literals_list) {
    var length_down = 2 ** literals_list.length + 1
    var length_across = literals_list.length
    var top_labels = literals_list

    var truth_table = new Array(length_down)
    for (var i = 0; i < length_down; i++) {
        truth_table[i] = new Array(length_across)
    }
    truth_table[0] = top_labels

    for (var lit_num = 0; lit_num < length_across; lit_num++) {
        var num = 1
        var counter = 0
        var change_over = (2 ** (lit_num + 1)) - 1
        for (var i = 0; i < change_over + 1; i++) {
            var range = 2 ** (length_across - lit_num - 1)
            for (var n = 0; n < range; n++) {
                truth_table[n + i*(2 ** (length_across - lit_num - 1)) + 1][lit_num] = num
            }
            counter += 1
            if (num === 1) {
                num = 0
            } else {
                num = 1
            }
        }
    }
    return truth_table
}


function alter_table(truth_table, implication_list) {
    var temp_conjuntions = new Array(truth_table.length - 1)
    for (var i = 0; i < truth_table.length - 1; i++) {
        temp_conjuntions[i] = []
    }

    for (var i = 0; i < implication_list.length; i++) {
        var imp = implication_list[i]
        var pred_negated = false
        var cons_negated = false
        var pred
        var cons
        if (imp[0].startsWith('!')) {
            pred_negated = true
            pred = truth_table[0].indexOf(not_literal(imp[0]))
        } else {
            pred = truth_table[0].indexOf(imp[0])
        }
        if (imp[1].startsWith('!')) {
            cons_negated = true
            cons = truth_table[0].indexOf(not_literal(imp[1]))
        } else {
            cons = truth_table[0].indexOf(imp[1])
        }


        for (var n = 0; n < truth_table.length - 1; n++) {
            var row = truth_table[n + 1]
            if (pred_negated && cons_negated) {
                if (row[pred] === 1) {
                    temp_conjuntions[n].push('T')
                } else if (row[cons] === 1) {
                    temp_conjuntions[n].push('F')
                } else {
                    temp_conjuntions[n].push('T')
                }
            } else if (pred_negated) {
                if (row[pred] === 1) {
                    temp_conjuntions[n].push('T')
                } else if (row[cons] === 0) {
                    temp_conjuntions[n].push('F')
                } else {
                    temp_conjuntions[n].push('T')
                }
            } else if (cons_negated) {
                if (row[pred] === 0) {
                    temp_conjuntions[n].push('T')
                } else if (row[cons] === 1) {
                    temp_conjuntions[n].push('F')
                } else {
                    temp_conjuntions[n].push('T')
                }
            } else {
                if (row[pred] === 0) {
                    temp_conjuntions[n].push('T')
                } else if (row[cons] === 0) {
                    temp_conjuntions[n].push('F')
                } else {
                    temp_conjuntions[n].push('T')
                }
            }
        }
    }

    var output = []
    for (var i = 0; i < temp_conjuntions.length; i++) {
        var row = temp_conjuntions[i]
        var out = 'T'
        for (var n = 0; n < row.length; n++) {
            if (!(out === 'T' && row[n] === 'T')) {
                out = 'F'
            }
        }
        output.push(out)
    }

    for (var i = 0; i < truth_table.length - 1; i++) {
        truth_table[i + 1].push(output[i])
    }
    return truth_table
}




  

// Create Virtual Tree
function create_nodes(implication_list) {
    var nodes = {}
    var imp
    var pred
    var cons
    
    for (var i = 0; i < implication_list.length; i++) {
        // Normal Implication
        imp = implication_list[i]
        pred = imp[0]
        cons = imp[1]
        if (!(Object.keys(nodes).includes(pred))) {
            nodes[pred] = {
                nood: pred,
                children: [cons],
                parents: []
            }
        } else {
            nodes[pred].children.push(cons)
        }
        if (!(Object.keys(nodes).includes(cons))) {
            nodes[cons] = {
                nood: cons,
                children: [],
                parents: [pred]
            }
        } else {
            nodes[cons].parents.push(pred)
        }

        // // For Contra-Positive
        var contra = contra_positive(imp)
        pred = contra[0]
        cons = contra[1]
        if (!(Object.keys(nodes).includes(pred))) {
            nodes[pred] = {
                nood: pred,
                children: [cons],
                parents: []
            }
        } else {
            nodes[pred].children.push(cons)
        }
        if (!(Object.keys(nodes).includes(cons))) {
            nodes[cons] = {
                nood: cons,
                children: [],
                parents: [pred]
            }
        } else {
            nodes[cons].parents.push(pred)
        }
    }
    return nodes
}

function new_join_nodes(nodes_object) {
    var output = []
    var keys = Object.keys(nodes_object)
    while (keys.length !== 0) {
        var current_key = keys.pop()
        var nodes_to_check = []
        var nodes_added = [current_key]
        var temp_tree = []
        var temp_node = nodes_object[current_key]
        temp_tree.push(temp_node)
        
        for (var i = 0; i < temp_node.children.length; i++) {
            nodes_to_check.push(temp_node.children[i])
        }
        for (var i = 0; i < temp_node.parents.length; i++) {
            nodes_to_check.push(temp_node.parents[i])
        }
        
        while (nodes_to_check.length !== 0) {
            var temp_index = nodes_to_check.pop()
            nodes_added.push(temp_index)
            temp_node = nodes_object[temp_index]
            for (var i = 0; i < temp_node.children.length; i++) {
                if (!(nodes_added.includes(temp_node.children[i]))) {
                    if (!(nodes_to_check.includes(temp_node.children[i]))) {
                        nodes_to_check.push(temp_node.children[i])
                    }
                }
            }
            for (var i = 0; i < temp_node.parents.length; i++) {
                if (!(nodes_added.includes(temp_node.parents[i]))) {
                    if (!(nodes_to_check.includes(temp_node.parents[i]))) {
                        nodes_to_check.push(temp_node.parents[i])
                    }    
                }
            }
            temp_tree.push(temp_node)
            temp_index = keys.indexOf(temp_index)
            if (temp_index > -1) {
                keys.splice(temp_index, 1)
            }
        }
       
        output.push(temp_tree)
    }
    return output
}

function combine_tree_pairs(tree_list) {
    var temp_tree = tree_list.pop()
    var nodes_in_each = [[]]
    for (var i = 0; i < temp_tree.length; i++) {
        nodes_in_each[0].push(temp_tree[i].nood)
    }
    var output = [[temp_tree]]

    for (var i = 0; i < tree_list.length; i++) {
        var to_add = true
        temp_tree = tree_list[i]
        var temp_tree_copy = temp_tree.slice()
        var temp_node = temp_tree_copy.pop()
        var literal = not_literal(temp_node.nood)
        for (var n = 0; n < nodes_in_each.length; n++) {
            if (nodes_in_each[n].includes(literal)) {
                output[n].push(temp_tree)
                to_add = false
                for (var j = 0; j < temp_tree.length; j++) {
                    nodes_in_each[n].push(temp_tree[j].nood)
                }
                break
            } else if (nodes_in_each[n].includes(not_literal(literal))) {
                to_add = false
                break
            }
        }
        if (to_add) {
            output.push([temp_tree])
            temp_list = []
            for (var n = 0; n < temp_tree.length; n++) {
                temp_list.push(temp_tree[n].nood)
            }
            nodes_in_each.push(temp_list)
        }
    }
    return output
}

function produce_valid_trees(tree_list) {
    var output = []
    var imp_list = get_literals()
    for (var i = 0; i < tree_list.length; i++) {
        for (var n = 0; n < tree_list[i].length; n++) {
            outer:
            for (var j = 0; j < tree_list[i][n].length; j++) {
                for (var k = 0; k < imp_list.length; k++) {
                    if (imp_list[k].includes(tree_list[i][n][j].nood)) {
                        output.push(tree_list[i][n])
                        break outer
                    }
                }
            }
        }
    }
    return output
}



function create_links(tree) {
    var output = []
    for (var j = 0; j < tree.length; j++) {
        for (var i = 0; i < tree[j].length; i++) {
            if (tree[j][i].children.length === 0) {
                output.push({
                    source: tree[j][i].nood,
                    target: 'T'
                })
            } else {
                for (var n = 0; n < tree[j][i].children.length; n++) {
                    output.push({
                        source: tree[j][i].nood,
                        target: tree[j][i].children[n]
                    })
                }
            }
            if (tree[j][i].parents.length === 0) {
                output.push({
                    source: 'F',
                    target: tree[j][i].nood
                })
            }
        }
    }
    
    return output
}


// SIMPLE FUNCTION TO REMOVE PREVIOUS TREE
function removePrevTree() {
    var container = document.getElementById("tree")
    while (container.firstChild) {
        container.removeChild(container.firstChild)
    }
}



// MAIN FUNCTION TO GENERATE TREE
function generateTree(tree_pairs) {
    removePrevTree()

    var validStates = document.getElementById('valid-states')
    while (validStates.firstChild) {
        validStates.removeChild(validStates.firstChild)
    }

    document.getElementById('total-evaluations').textContent = ''

    var width = 1200,
        height = 450
    var evaluated = false

    // // Get the data for the tree
    var circles_list = []
    for (var i = 0; i < tree_pairs.length; i++) {
        for (var n = 0; n < tree_pairs[i].length; n++) {
            tree_pairs[i][n].width = 960 * ((i + 1) / (tree_pairs.length + 1))
            tree_pairs[i][n].height = 500 * ((n + 1) / (tree_pairs[i].length + 1)) - 20
            circles_list.push(tree_pairs[i][n])
        }
    }
    // Create links from this data
    var links = create_links(tree_pairs)

    // Create circles for each of these nodes
    var nodes = d3.range(circles_list.length).map(function(i) {
    return {
        id: circles_list[i].nood,
        x: circles_list[i].width + (Math.floor(Math.random() * 10)),
        y: circles_list[i].height,
        r: 15,
        category: 0
    };
    });

    nodes.push({
        id:'T',
        x: 2 * width / 5,
        y: 20,
        r: 20,
        category: 1
    })

    nodes.push({
        id:'F',
        x: 2 * width / 5,
        y: height + 15,
        r: 20,
        category: 2
    })


    // Append the svg element
    var colors = d3.scaleOrdinal(d3.schemeCategory20);
    var yCenters = [250, 125, 325]

    var svg = d3.select("#tree").append("svg")
    .attr("preserveAspectRatio", "xMinYMin meet")
    .attr("viewBox", "0 0 960 500")
    .call(d3.zoom().on("zoom", function () {
        svg.attr("transform", d3.event.transform)
    })).append('g')


    svg.append('defs').append('marker')
    .attr('id', 'arrowhead')
    .attr('viewBox', '-0 -5 10 10')
    .attr('refX', 17)
    .attr('refY', 0)
    .attr('orient', 'auto')
    .attr('markerWidth', 6)
    .attr('markerHeight', 6)
    .attr('xoverflow', 'visible')
    .append('svg:path')
    .attr('d', 'M 0,-5 L 10 ,0 L 0,5')
    .attr('fill', '#999')
    .style('stroke','none');

    var simulation = d3.forceSimulation()
        .force("link", d3.forceLink().id(function (d) {return d.id;}).distance(5).strength(0.25))
        .force("charge", d3.forceManyBody().strength(-650))
        .force('y', d3.forceY().y(function(d) {
            return height/2
        }).strength(0.015))
        .force('x', d3.forceX().x(function(d){return 2 * width / 5}).strength(0.05))

    var link = svg.selectAll(".link")
    .data(links)
    .enter()
    .append("line")
    .attr("class", "link")
    .attr('marker-end','url(#arrowhead)')

    node = svg.selectAll(".node")
        .data(nodes)
        .enter()
        .append("g")
        .attr("class", function(d) {
            if (d.id === 'T' || d.id === 'F') {
                return "node stuck"
            } else {
                return "node unstuck"
            }
        }).attr('id', function(d) {
            if (d.id.length > 1) {
                return 'not' + d.id[d.id.length - 1]
            } else {
                return d.id
            }
        })
        .call(d3.drag()
                .on("start", dragstarted)
                .on("drag", dragged)
                // .on("end", dragended)
        )
        .on("click", function(d) {
            d3.select(this).classed("stuck", d3.select(this).classed("stuck") ? false : true)
            d3.select(this).classed("unstuck", d3.select(this).classed("unstuck") ? false : true)
            toggleStick(d)
          })

    node.append("circle")
        .attr("r", function(d) { return d.r })
        .style("fill", function (d, i) {
            if (d.id === 'T') {
                return 'lightgreen'
            } else if (d.id === 'F'){
                return 'red'
            } else {
                return 'lightblue'
            }
            
        })

    node.append("text")
        .attr("dy", 3)
        .attr('dx', -5)
        .text(function (d) {return d.id});

    simulation
        .nodes(nodes)
        .on("tick", ticked);

    simulation.force("link")
        .links(links);

    node.each(function(d) {
        if (d.id === 'T' || d.id === 'F') {
            d.fx = d.x
            d.fy = d.y
        }
    })
    
    function ticked() {
        link
            .attr("x1", function (d) {return d.source.x;})
            .attr("y1", function (d) {return d.source.y;})
            .attr("x2", function (d) {return d.target.x;})
            .attr("y2", function (d) {return d.target.y;});

        node
            .attr("transform", function (d) {return "translate(" + d.x + ", " + d.y + ")"})   
    }

    function dragstarted(d) {
        if (!d3.event.active) simulation.alphaTarget(0.3).restart()
    }

    function dragged(d) {
        if (d.fx) {
            d.fx = d3.event.x
            d.fy = d3.event.y
        } else {
            d.x = d3.event.x;
            d.y = d3.event.y;
        }
    }

    function toggleStick(d) {
        if (d.fx) {
            d.fy = null
            d.fx = null
        } else {
            d.fx = d.x
            d.fy = d.y
        }     
    }

    // FUNCTION USED TO ALTER THE TREE
    function highlightTree(e) {
        var temp = e.target.textContent.split("\xa0")
        var children = document.querySelectorAll('.table-entry')
        for (var i = 0; i < children.length; i++) {
            children[i].className = 'table-entry table-hover'
        }
        e.target.classList.add('activated')
        e.target.classList.remove('table-hover')
        var values = []
        for (var i = 0; i < temp.length; i++) {
            if (!(temp[i] === "")) {
                values.push(temp[i])
            }
        }
        temp = document.getElementById('tableTitle').textContent.split('\xa0')
        var lits = []
        for (var i = 0; i < temp.length; i++) {
            if (!(temp[i] === "")) {
                lits.push(temp[i])
            }
        }
    
        for (var i = 0; i < lits.length; i++) {
            var node = d3.select('#' + lits[i])
            var not_node = d3.select('#not' + lits[i])
            
            if (values[i] === '1') {
                node.each(function(d) { 
                    d.category = 1
                })
                if (not_node) {
                    not_node.each(function(d) { 
                        d.category = 2
                        
                    })
                }
            } else {
                node.each(function(d) { 
                    d.category = 2
                })
                if (not_node) {
                    not_node.each(function(d) { 
                        d.category = 1
                    })
                }
            }
        }
        
        // Physics which move nodes
        checkPhysics()

        link.style('stroke', 'black')
        d3.selectAll('circle').style('fill', function(d) {
            if (d.id === 'T') {
                return 'lightgreen'
            } else if (d.id === 'F') {
                return 'red'
            } else {
                if (d.category === 1) {
                    return 'lightgreen'
                } else {
                    return 'red'
                }
            }
        })
    }

    function evaluateGraph() {
        if (simulation) {
            link.style('stroke', function(d) {
                if (d.source.category === d.target.category) {
                    return 'green'
                } else if (d.source.category < d.target.category) {
                    return 'red'
                } else {
                    return 'green'
                }
            })
        }
    }

    function removeAll() {
        var container = document.getElementById("truthtable")
        while (container.firstChild) {
            container.removeChild(container.firstChild)
        }
        var title_container = document.getElementById("tableTitle")
        while (title_container.firstChild) {
            title_container.removeChild(title_container.firstChild)
        }
        
    }

    function generate() {
        removeAll()
        var inputs = document.querySelectorAll('.litInput')
        var imp_list = []
        for (var i = 0; i < inputs.length; i++) {
            var temp_list = inputs[i].value.split(" ")
            imp_list.push([temp_list[0], temp_list[temp_list.length - 1]])
        }
        console.log("Generate Table")
        var table = alter_table(produce_truth_table(countLiterals(imp_list)), imp_list)
        var container = document.getElementById("truthtable")
        var title_container = document.getElementById("tableTitle")
        var new_element = document.createElement("span")
        new_element.textContent = '\xa0\xa0'
        new_element.classList.add('table-title')
        for (var i = 0; i < table[0].length; i++) {
            new_element.textContent = new_element.textContent + table[0][i] + '\xa0\xa0\xa0'
        }
        title_container.appendChild(new_element)
        
        for (var i = 1; i < table.length; i++) {
            var new_element = document.createElement("span")
            new_element.classList.add('table-entry')
            new_element.classList.add('table-hover')
            new_element.textContent = '\xa0\xa0\xa0'
            for (var n = 0; n < table[i].length - 1; n++) {
                new_element.textContent = new_element.textContent + table[i][n] + '\xa0\xa0\xa0'
            }
            var br = document.createElement("br")
    
            new_element.addEventListener("click", function(e) {
                highlightTree(e)
            })
            
    
            container.appendChild(new_element)
    
            var answer = document.createElement('span')
            answer.classList.add('answer')
            answer.textContent = table[i][table[i].length - 1]
            container.appendChild(answer)
    
            container.appendChild(br)
        }
    }

    function checkPhysics() {
        if (document.getElementById('physics').checked) {
            simulation.force('y', d3.forceY().y(function(d) {
                return yCenters[d.category]
            }).strength(1))
            simulation.force("y").initialize(nodes)
            if (!document.querySelector('.cut')) {
                svg.append('line').attr('class', 'cut')
                .attr('x1', 0).attr('y1', height/2)
                .attr('x2', width).attr('y2', height/2)
                .attr('stroke-width', 1).attr('stroke', 'black')
                
                svg.append('text').attr('y', height/2 - 20).attr('x', 100).attr('class', 'cut-true').style('fill', 'green').text('True')
                svg.append('text').attr('y', height/2 + 30).attr('x', 100).attr('class', 'cut-false').style('fill', 'red').text('False')
            } 

        } else {
            simulation.force('y', d3.forceY().y(function(d) {
                return height/2
            }).strength(0.015))
            simulation.force('y').initialize(nodes)

            d3.select('.cut').remove()
            d3.select('.cut-true').remove()
            d3.select('.cut-false').remove()
        }
    }

    function totalEvaluations() {
        var total = 0
        var answers = document.querySelectorAll('.answer')
        var states = [[document.getElementById('tableTitle').textContent]]
        for (var i = 0; i < answers.length; i++) {
            if (answers[i].textContent === 'T') {
                total += 1
                states.push(answers[i].previousElementSibling.textContent)
            }
        }
        document.getElementById('total-evaluations').textContent = total
        var statesHTML = document.getElementById('valid-states')
        statesHTML.textContent = states[0]
        // var br = document.createElement("br")
        // statesHTML.appendChild(br)
        for (var i = 1; i < states.length; i++) {
            var entry = document.createElement('div')
            entry.textContent = states[i]
            statesHTML.appendChild(entry)
            //statesHTML.appendChild(br)
        }

    }

    generate()
    document.getElementById("evaluateTreeButton").addEventListener("click", function() {
        evaluateGraph()
        if (document.querySelector('.activated')) {
            if (document.querySelector('.activated').nextElementSibling.textContent == 'T') {
                document.querySelector('.activated').className = 'table-entry correct'
            } else {
                document.querySelector('.activated').className = 'table-entry false'
            }
        }
    })

    document.getElementById('physics').addEventListener('change', function() {
        checkPhysics()
    })

    document.getElementById('totalButton').addEventListener('click', function() {
        totalEvaluations()
    })
}


function get_literals() {
    var inputs = document.querySelectorAll('.litInput')
    var imp_list = []
    for (var i = 0; i < inputs.length; i++) {
        var temp_list = inputs[i].value.split(" ")
        var corrected = []
        for (var n = 0; n < temp_list.length; n++) {
            if (!(temp_list[n] === '')) {
                corrected.push(temp_list[n])
            }
        }
        if (!corrected.includes('->')) {
            alert('Please include ->')
            return []
        } else if (corrected.includes('T')){
            alert('Please do not use the literal T')
            return []
        } else if (corrected.includes('F')) {
            alert('Please do not use the literal F')
            return []
        } else {
            imp_list.push([corrected[0], corrected[corrected.length - 1]])
        }
        
    }
    return imp_list
}

document.getElementById("generateTreeButton").addEventListener("click", function() {
    generateTree(produce_valid_trees(combine_tree_pairs(new_join_nodes(create_nodes(get_literals())))))
    
})


